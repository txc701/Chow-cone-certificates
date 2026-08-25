"""Exact d=4 equality gate for the oriented lift of the degree-four ansatz.

The lift starts from the 156 committed columns.  Every column supported on
unbalanced edges is split into its left and right restrictions.  Balanced
columns are already self-reversing and remain single.  No new raw feature,
certificate coordinate, nonnegativity constraint, or dimension is added.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from k4_degree4_decision import (
    DecisionSystem,
    PEEL_WIDTHS,
    balanced_invariant_basis,
    evaluate_polynomial,
    evaluate_sparse_row,
    exact_eliminate,
    fraction_record,
    normalized_flow_row,
    parameter_names as old_parameter_names,
    symmetry_basis,
    system_ranks,
    verify_solution,
)
from k4_feature_analysis import EdgeFeatures, edge_features
from k4_weights import s4
from support import support_compositions


CHECKPOINT_BASE = "59560a535c7c1ae3201a44215053ac24cc50b803"
D4 = 4
CORRESPONDENCE_SCHEMA = "chow-cone/k4-desymmetrized-correspondence/v1"
SYSTEM_SCHEMA = "chow-cone/k4-desymmetrized-d4-system/v1"
DECISION_SCHEMA = "chow-cone/k4-desymmetrized-d4-decision/v1"
MANIFEST_SCHEMA = "chow-cone/k4-desymmetrized-d4-manifest/v1"

SparseRow = dict[int, Fraction]


def _feature_values(feature: EdgeFeatures) -> tuple[int, ...]:
    return (
        feature.z,
        feature.L,
        feature.R,
        feature.VL,
        feature.VR,
        feature.QL,
        feature.QR,
    )


def lifted_parameter_names() -> tuple[str, ...]:
    basis = symmetry_basis()
    balanced = balanced_invariant_basis()
    names = []
    for peel in PEEL_WIDTHS:
        for side in ("left", "right"):
            names.extend(
                f"s{peel}:{side}:invariant:{index:02d}"
                for index in range(len(basis.invariant))
            )
            names.extend(
                f"s{peel}:{side}:anti:{index:02d}"
                for index in range(len(basis.anti_invariant))
            )
        names.extend(
            f"s{peel}:balanced:invariant:{index:02d}"
            for index in range(len(balanced))
        )
    return tuple(names)


def _offsets(peel_width: int) -> dict[str, int]:
    if peel_width not in PEEL_WIDTHS:
        raise ValueError("peel width must be 2 or 3")
    basis = symmetry_basis()
    balanced = balanced_invariant_basis()
    oriented = len(basis.invariant) + len(basis.anti_invariant)
    per_peel = 2 * oriented + len(balanced)
    start = PEEL_WIDTHS.index(peel_width) * per_peel
    return {
        "left_invariant": start,
        "left_anti": start + len(basis.invariant),
        "right_invariant": start + oriented,
        "right_anti": start + oriented + len(basis.invariant),
        "balanced_invariant": start + 2 * oriented,
    }


def lifted_normalized_flow_row(feature: EdgeFeatures) -> SparseRow:
    """Return the exact coefficient row in the 276-column oriented lift."""
    basis = symmetry_basis()
    balanced = balanced_invariant_basis()
    values = _feature_values(feature)
    offsets = _offsets(feature.peel_width)
    row: SparseRow = {}
    if feature.peel_side == "balanced":
        start = offsets["balanced_invariant"]
        for index, polynomial in enumerate(balanced):
            value = evaluate_polynomial(polynomial, values)
            if value:
                row[start + index] = Fraction(value)
        return row
    if feature.peel_side not in {"left", "right"}:
        raise ValueError(f"unknown peel side {feature.peel_side!r}")
    invariant_start = offsets[f"{feature.peel_side}_invariant"]
    anti_start = offsets[f"{feature.peel_side}_anti"]
    anti_sign = 1 if feature.peel_side == "left" else -1
    for index, polynomial in enumerate(basis.invariant):
        value = evaluate_polynomial(polynomial, values)
        if value:
            row[invariant_start + index] = Fraction(value)
    for index, polynomial in enumerate(basis.anti_invariant):
        value = anti_sign * evaluate_polynomial(polynomial, values)
        if value:
            row[anti_start + index] = Fraction(value)
    return row


def correspondence_table() -> tuple[dict[str, Any], ...]:
    new_names = lifted_parameter_names()
    new_index = {name: index for index, name in enumerate(new_names)}
    rows: dict[str, dict[str, Any]] = {}
    basis = symmetry_basis()
    balanced = balanced_invariant_basis()
    for peel in PEEL_WIDTHS:
        for index in range(len(basis.invariant)):
            old_name = f"s{peel}:oriented:invariant:{index:02d}"
            terms = [
                f"s{peel}:left:invariant:{index:02d}",
                f"s{peel}:right:invariant:{index:02d}",
            ]
            rows[old_name] = {
                "old_name": old_name,
                "old_kind": "oriented_invariant",
                "new_terms": [
                    {"column": new_index[name], "name": name, "factor": "1"}
                    for name in terms
                ],
                "fixed_relation": f"coefficient({terms[0]})=coefficient({terms[1]})",
            }
        for index in range(len(basis.anti_invariant)):
            old_name = f"s{peel}:oriented:anti:{index:02d}"
            terms = [
                f"s{peel}:left:anti:{index:02d}",
                f"s{peel}:right:anti:{index:02d}",
            ]
            rows[old_name] = {
                "old_name": old_name,
                "old_kind": "oriented_anti_with_side_sign",
                "new_terms": [
                    {"column": new_index[name], "name": name, "factor": "1"}
                    for name in terms
                ],
                "fixed_relation": f"coefficient({terms[0]})=coefficient({terms[1]})",
            }
        for index in range(len(balanced)):
            old_name = f"s{peel}:balanced:invariant:{index:02d}"
            rows[old_name] = {
                "old_name": old_name,
                "old_kind": "genuinely_self_reversing_balanced",
                "new_terms": [
                    {
                        "column": new_index[old_name],
                        "name": old_name,
                        "factor": "1",
                    }
                ],
                "fixed_relation": "single fixed column",
            }
    ordered = tuple(rows[name] for name in old_parameter_names())
    if len(ordered) != len(old_parameter_names()):
        raise AssertionError("correspondence table is incomplete")
    return ordered


def coefficient_reflection_permutation() -> tuple[int, ...]:
    names = lifted_parameter_names()
    by_name = {name: index for index, name in enumerate(names)}
    reflected = []
    for name in names:
        fields = name.split(":")
        if fields[1] == "left":
            fields[1] = "right"
            reflected.append(by_name[":".join(fields)])
        elif fields[1] == "right":
            fields[1] = "left"
            reflected.append(by_name[":".join(fields)])
        elif fields[1] == "balanced":
            reflected.append(by_name[name])
        else:
            raise AssertionError("unknown lifted parameter channel")
    return tuple(reflected)


def reflect_lifted_coefficients(
    coefficients: Sequence[Fraction],
) -> tuple[Fraction, ...]:
    names = lifted_parameter_names()
    if len(coefficients) != len(names):
        raise ValueError("lifted coefficient vector has the wrong length")
    permutation = coefficient_reflection_permutation()
    return tuple(Fraction(coefficients[index]) for index in permutation)


def embed_old_coefficients(
    coefficients: Sequence[Fraction],
) -> tuple[Fraction, ...]:
    old_names = old_parameter_names()
    if len(coefficients) != len(old_names):
        raise ValueError("old coefficient vector has the wrong length")
    lifted = [Fraction(0) for _ in lifted_parameter_names()]
    table = correspondence_table()
    for value, record in zip(coefficients, table):
        value = Fraction(value)
        for term in record["new_terms"]:
            lifted[term["column"]] += value * Fraction(int(term["factor"]))
    return tuple(lifted)


def recover_old_coefficients(
    coefficients: Sequence[Fraction],
) -> tuple[Fraction, ...]:
    values = tuple(Fraction(value) for value in coefficients)
    if reflect_lifted_coefficients(values) != values:
        raise ValueError("lifted coefficients are not in the fixed subspace")
    recovered = []
    for record in correspondence_table():
        recovered.append(values[record["new_terms"][0]["column"]])
    recovered_tuple = tuple(recovered)
    if embed_old_coefficients(recovered_tuple) != values:
        raise AssertionError("fixed-subspace recovery failed")
    return recovered_tuple


def fixed_subspace_dimension() -> int:
    permutation = coefficient_reflection_permutation()
    seen = set()
    cycles = 0
    for index in range(len(permutation)):
        if index in seen:
            continue
        seen.add(index)
        seen.add(permutation[index])
        cycles += 1
    return cycles


def _add_scaled(
    target: SparseRow,
    source: Mapping[int, Fraction],
    scale: Fraction,
) -> None:
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        elif column in target:
            del target[column]


def build_d4_system() -> DecisionSystem:
    """Build only the authorized d=4 exact equality system."""
    compositions = tuple(sorted(support_compositions(D4)))
    local_rows: dict[tuple[int, ...], SparseRow] = {
        composition: {} for composition in compositions
    }
    features = edge_features(D4)
    for feature in features:
        edge_row = lifted_normalized_flow_row(feature)
        _add_scaled(local_rows[feature.parent], edge_row, feature.ratio)
        _add_scaled(local_rows[feature.child], edge_row, Fraction(-1))
    return DecisionSystem(
        dimensions=(D4,),
        parameter_names=lifted_parameter_names(),
        row_labels=tuple((D4, composition) for composition in compositions),
        rows=tuple(local_rows[composition] for composition in compositions),
        rhs=tuple(Fraction(s4(composition)) for composition in compositions),
        n_edges=len(features),
    )


def lifted_witness_row(system: DecisionSystem) -> tuple[SparseRow, Fraction]:
    multipliers = {(2, 2, 2): -1, (2, 4): 2, (4, 2): -2}
    rows = {
        composition: row
        for (_, composition), row in zip(system.row_labels, system.rows)
    }
    rhs = {
        composition: value
        for (_, composition), value in zip(system.row_labels, system.rhs)
    }
    combined: SparseRow = {}
    combined_rhs = Fraction(0)
    for composition, multiplier in multipliers.items():
        _add_scaled(combined, rows[composition], Fraction(multiplier))
        combined_rhs += multiplier * rhs[composition]
    return combined, combined_rhs


def correspondence_document() -> dict[str, Any]:
    basis = symmetry_basis()
    balanced = balanced_invariant_basis()
    permutation = coefficient_reflection_permutation()
    names = lifted_parameter_names()
    return {
        "schema": CORRESPONDENCE_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "construction": (
            "restrict each old oriented column to independent left and right "
            "channels; retain each self-reversing balanced column once"
        ),
        "maximum_weighted_degree": 4,
        "peel_widths": list(PEEL_WIDTHS),
        "counts": {
            "old_parameters": len(old_parameter_names()),
            "oriented_basis_per_side_per_peel": (
                len(basis.invariant) + len(basis.anti_invariant)
            ),
            "balanced_self_reversing_per_peel": len(balanced),
            "new_parameters_per_peel": (
                2 * (len(basis.invariant) + len(basis.anti_invariant))
                + len(balanced)
            ),
            "new_parameters": len(names),
            "fixed_subspace_dimension": fixed_subspace_dimension(),
        },
        "right_anti_convention": (
            "the right restriction retains the minus sign already present "
            "in the old global anti-invariant column"
        ),
        "phi_G_appended": False,
        "parameter_names": list(names),
        "coefficient_reflection": [
            {
                "column": index,
                "name": names[index],
                "reflected_column": reflected,
                "reflected_name": names[reflected],
            }
            for index, reflected in enumerate(permutation)
        ],
        "old_to_new": list(correspondence_table()),
    }


def system_document(system: DecisionSystem) -> dict[str, Any]:
    rows = []
    for index, ((d, composition), row, rhs) in enumerate(
        zip(system.row_labels, system.rows, system.rhs)
    ):
        rows.append(
            {
                "row": index,
                "d": d,
                "composition": list(composition),
                "entries": [
                    [column, str(value.numerator), str(value.denominator)]
                    for column, value in sorted(row.items())
                ],
                "rhs": fraction_record(rhs),
            }
        )
    return {
        "schema": SYSTEM_SCHEMA,
        "method": "direct exact d=4 normalized divergence substitution",
        "dimensions": [D4],
        "n_rows": len(system.rows),
        "n_columns": len(system.parameter_names),
        "n_edges": system.n_edges,
        "n_nonzero_entries": sum(len(row) for row in system.rows),
        "parameter_names": list(system.parameter_names),
        "rows": rows,
    }


def decision_document(system: DecisionSystem) -> dict[str, Any]:
    result = exact_eliminate(system)
    coefficient_rank, augmented_rank = system_ranks(system)
    if result.status != "consistent" or result.solution is None:
        raise RuntimeError("the bounded d=4 lifted equality system is inconsistent")
    verification = verify_solution(system, result.solution)
    if not verification["verified"]:
        raise AssertionError("exact lifted solution has nonzero residual")
    residuals = []
    for (_, composition), row, rhs in zip(
        system.row_labels, system.rows, system.rhs
    ):
        residual = evaluate_sparse_row(row, result.solution) - rhs
        residuals.append(
            {"composition": list(composition), "residual": fraction_record(residual)}
        )
    sparse_solution = [
        {
            "column": index,
            "name": system.parameter_names[index],
            "value": fraction_record(value),
        }
        for index, value in enumerate(result.solution)
        if value
    ]
    witness_row, witness_rhs = lifted_witness_row(system)
    return {
        "schema": DECISION_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "scope": {
            "dimensions": [D4],
            "equality_only": True,
            "nonnegativity_optimization_run": False,
            "holdouts_run": False,
            "phi_G_appended": False,
        },
        "matrix": {
            "n_rows": len(system.rows),
            "n_columns": len(system.parameter_names),
            "n_edges": system.n_edges,
            "coefficient_rank": coefficient_rank,
            "augmented_rank": augmented_rank,
            "nullity": len(system.parameter_names) - coefficient_rank,
        },
        "equality_status": result.status,
        "solution": {
            "method": "exact sparse echelon solve; free parameters set to zero",
            "nonzero_coefficients": sparse_solution,
            "residuals": residuals,
            "verification": verification,
        },
        "old_witness_after_untying": {
            "rhs": fraction_record(witness_rhs),
            "n_nonzero_columns": len(witness_row),
            "entries": [
                {
                    "column": column,
                    "name": system.parameter_names[column],
                    "value": fraction_record(value),
                }
                for column, value in sorted(witness_row.items())
            ],
            "interpretation": (
                "a linear condition on all displayed untied columns, not a "
                "distinguished phi_G coefficient"
            ),
        },
        "stopping_rule": (
            "stop after the d=4 equality decision; do not optimize edge "
            "nonnegativity or evaluate another dimension"
        ),
    }


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


def run_d4_gate(output_dir: str | Path) -> dict[str, Any]:
    root = Path(output_dir)
    root.mkdir(parents=True, exist_ok=True)
    system = build_d4_system()
    documents = {
        "basis_correspondence.json": correspondence_document(),
        "system.json": system_document(system),
        "decision.json": decision_document(system),
    }
    for name, document in documents.items():
        _write_json(root.joinpath(name), document)
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "files": [
            {"path": name, "sha256": _sha256(root.joinpath(name))}
            for name in sorted(documents)
        ],
        "scope": "d=4 equality only",
    }
    _write_json(root.joinpath("manifest.json"), manifest)
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args(argv)
    manifest = run_d4_gate(args.output_dir)
    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
