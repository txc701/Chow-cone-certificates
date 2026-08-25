"""Run exactly one bounded k=4 weighted-degree-four decision experiment."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from k4_degree4_decision import (
    BASIS_SCHEMA,
    HOLDOUT_DIMENSIONS,
    RESULT_SCHEMA,
    SOLUTION_SCHEMA,
    SYSTEM_SCHEMA,
    TRAINING_DIMENSIONS,
    WITNESS_SCHEMA,
    basis_document,
    build_decision_system,
    exact_eliminate,
    parameter_names,
    primitive_integer_witness,
    solution_document,
    system_document,
    system_ranks,
    witness_document,
)
from verify_k4_degree4_decision import verify_artifact_directory


VERIFICATION_SCHEMA = "chow-cone/k4-degree4-verification-summary/v1"
MANIFEST_SCHEMA = "chow-cone/k4-degree4-manifest/v1"
CHECKPOINT_BASE = "f3efcfd4fa718884ed9934590af83f46c0772a00"


def _write_json(path: Path, document: Any) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _source_provenance() -> list[dict[str, str]]:
    source_dir = Path(__file__).resolve().parent
    names = (
        "k4_degree4_decision.py",
        "k4_feature_analysis.py",
        "k4_weights.py",
        "run_k4_degree4_decision.py",
        "support.py",
        "verify_k4_degree4_decision.py",
    )
    return [
        {
            "path": f"src/{name}",
            "sha256": _sha256(source_dir.joinpath(name)),
        }
        for name in names
    ]


def run_decision(output_dir: str | Path) -> dict[str, Any]:
    """Run the frozen d=2..12 training problem and persist exact evidence."""
    root = Path(output_dir)
    root.mkdir(parents=True, exist_ok=True)

    basis = basis_document()
    if basis["parameter_count"] != len(parameter_names()):
        raise RuntimeError("basis parameter count is internally inconsistent")
    basis_path = root.joinpath("basis.json")
    _write_json(basis_path, basis)

    training_system = build_decision_system(TRAINING_DIMENSIONS)
    training_path = root.joinpath("training_system.json")
    _write_json(training_path, system_document(training_system))

    smallest_inconsistent = None
    inconsistent_system = None
    inconsistent_elimination = None
    prefix_diagnostics = []
    for top_dimension in TRAINING_DIMENSIONS:
        prefix_dimensions = tuple(
            d for d in TRAINING_DIMENSIONS if d <= top_dimension
        )
        prefix_system = build_decision_system(prefix_dimensions)
        elimination = exact_eliminate(prefix_system)
        coefficient_rank, augmented_rank = system_ranks(prefix_system)
        prefix_diagnostics.append(
            {
                "dimensions": list(prefix_dimensions),
                "maximum_dimension": top_dimension,
                "equality_status": elimination.status,
                "coefficient_rank": coefficient_rank,
                "augmented_rank": augmented_rank,
                "n_rows": len(prefix_system.rows),
                "n_edges": prefix_system.n_edges,
            }
        )
        if elimination.status == "inconsistent":
            smallest_inconsistent = top_dimension
            inconsistent_system = prefix_system
            inconsistent_elimination = elimination
            break

    if (
        smallest_inconsistent is None
        or inconsistent_system is None
        or inconsistent_elimination is None
        or inconsistent_elimination.witness is None
    ):
        raise RuntimeError(
            "the frozen equality experiment unexpectedly remained consistent; "
            "no feature enlargement or fallback search is authorized"
        )

    integer_witness, witness_rhs = primitive_integer_witness(
        inconsistent_elimination.witness,
        inconsistent_system.rhs,
    )
    witness = witness_document(
        inconsistent_system,
        integer_witness,
        smallest_inconsistent_dimension=smallest_inconsistent,
    )
    if witness["verification"]["rhs_sum"] != {
        "num": str(witness_rhs),
        "den": "1",
    }:
        raise RuntimeError("witness RHS normalization mismatch")
    witness_path = root.joinpath("inconsistency_witness.json")
    _write_json(witness_path, witness)

    preceding_dimensions = tuple(
        d for d in TRAINING_DIMENSIONS if d < smallest_inconsistent
    )
    preceding_system = build_decision_system(preceding_dimensions)
    preceding_elimination = exact_eliminate(preceding_system)
    if (
        preceding_elimination.status != "consistent"
        or preceding_elimination.solution is None
    ):
        raise RuntimeError("the preceding training prefix is not consistent")
    preceding_solution = solution_document(
        preceding_system,
        preceding_elimination.solution,
    )
    preceding_path = root.joinpath("preceding_prefix_solution.json")
    _write_json(preceding_path, preceding_solution)

    full_coefficient_rank, full_augmented_rank = system_ranks(training_system)
    decision = {
        "schema": RESULT_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "training_dimensions": list(TRAINING_DIMENSIONS),
        "holdout_dimensions": list(HOLDOUT_DIMENSIONS),
        "ansatz": {
            "description": (
                "complete full-reversal-invariant normalized-flow polynomial "
                "class of weighted degree at most 4"
            ),
            "parameter_count": len(training_system.parameter_names),
            "certificate_coordinates_used": False,
            "construction": (
                "direct substitution into exact normalized divergence equations"
            ),
        },
        "training_problem": {
            "n_rows": len(training_system.rows),
            "n_edges": training_system.n_edges,
            "n_parameters": len(training_system.parameter_names),
            "coefficient_rank": full_coefficient_rank,
            "augmented_rank": full_augmented_rank,
        },
        "equality_status": "inconsistent",
        "smallest_inconsistent_dimension": smallest_inconsistent,
        "prefix_diagnostics": prefix_diagnostics,
        "witness": {
            "path": "inconsistency_witness.json",
            "n_nonzero_multipliers": len(witness["multipliers"]),
            "rhs_sum": witness["verification"]["rhs_sum"],
        },
        "preceding_consistent_prefix": {
            "dimensions": list(preceding_dimensions),
            "path": "preceding_prefix_solution.json",
            "verified": True,
        },
        "nonnegativity_status": "infeasible_a_fortiori",
        "nonnegativity_explanation": (
            "no coefficient vector satisfies the divergence equalities, so "
            "none can satisfy those equalities together with edgewise "
            "nonnegativity"
        ),
        "holdout_status": "not_run_no_training_solution",
        "holdout_explanation": (
            "the frozen rule requires holdout evaluation only for a feasible "
            "training coefficient vector; no such vector exists"
        ),
        "stopping_rule": (
            "stop after this decision; do not increase degree, add features, "
            "or launch another search"
        ),
    }
    decision_path = root.joinpath("decision.json")
    _write_json(decision_path, decision)

    verification = verify_artifact_directory(root)
    verification_document = {
        "schema": VERIFICATION_SCHEMA,
        "standalone_verifier": "src/verify_k4_degree4_decision.py",
        "verified": verification["verified"],
        "checks": verification,
    }
    verification_path = root.joinpath("verification_summary.json")
    _write_json(verification_path, verification_document)

    artifact_paths = (
        basis_path,
        training_path,
        witness_path,
        preceding_path,
        decision_path,
        verification_path,
    )
    files = [
        {
            "path": path.relative_to(root).as_posix(),
            "sha256": _sha256(path),
        }
        for path in artifact_paths
    ]
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "schemas": {
            "basis": BASIS_SCHEMA,
            "training_system": SYSTEM_SCHEMA,
            "inconsistency_witness": WITNESS_SCHEMA,
            "preceding_prefix_solution": SOLUTION_SCHEMA,
            "decision": RESULT_SCHEMA,
            "verification": VERIFICATION_SCHEMA,
            "manifest": MANIFEST_SCHEMA,
        },
        "fixed_parameters": {
            "training_dimensions": list(TRAINING_DIMENSIONS),
            "holdout_dimensions": list(HOLDOUT_DIMENSIONS),
            "maximum_weighted_degree": 4,
            "peel_width_maximum": 3,
            "arithmetic": "Python arbitrary-precision integers and Fraction",
            "certificate_coordinates_used": False,
        },
        "source_provenance": _source_provenance(),
        "files": files,
        "n_files_hashed": len(files),
        "manifest_self_hash": (
            "omitted because a file cannot contain its own SHA256 digest"
        ),
    }
    _write_json(root.joinpath("manifest.json"), manifest)
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args(argv)
    manifest = run_decision(args.output_dir)
    print(
        json.dumps(
            {
                "manifest": str(args.output_dir.joinpath("manifest.json")),
                "n_files_hashed": manifest["n_files_hashed"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
