"""Exact d=11 decision gate for the frozen 276-column shared ansatz.

The training system is the cumulative d=4,...,11 equality system.  The
committed d<=10 construction is imported unchanged.  Dimension 12 is built
only if the d<=11 coefficient matrix is consistent and has full rank, and in
that branch is evaluated strictly with the frozen unique vector.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from k4_degree4_decision import (
    DecisionSystem,
    evaluate_sparse_row,
    exact_eliminate,
    fraction_record,
    primitive_integer_witness,
    system_ranks,
    verify_solution,
)
from k4_desymmetrized_d4 import (
    lifted_normalized_flow_row,
    lifted_parameter_names,
)
from k4_desymmetrized_scan import (
    build_dimension_system,
    deduplicate_system,
    stack_systems,
    system_hashes,
    verify_inconsistency_witness,
)
from k4_feature_analysis import edge_features, g_value
from k4_weights import s4
from support import support_compositions


CHECKPOINT_BASE = "60b2fba4a4034e701ad38e344a4c2568ab834906"
TRAINING_DIMENSION = 11
CONDITIONAL_HOLDOUT_DIMENSION = 12
PARAMETER_COUNT = 276
GATE_SCHEMA = "chow-cone/k4-desymmetrized-d11-gate/v1"
D10_HASHES = {
    "matrix_sha256": "3ab29b5c8c4db6251272db846b18748bd4fb2757276e8261ebbab9e0de2c94af",
    "rhs_sha256": "b884de88fcdc4aa29a5ea8b0330d770c295cfeb5d6980f3cd650fc6f0bc0e1a8",
    "system_sha256": "74440aade255dd61367e0671bffdb490cbe9fb4a1af5b7f6e86f2a6de5d58a53",
}
SparseRow = dict[int, Fraction]


@dataclass(frozen=True)
class CoefficientEchelon:
    rank: int
    pivot_columns: tuple[int, ...]
    free_columns: tuple[int, ...]
    nullspace_basis: tuple[tuple[Fraction, ...], ...]


def _add_scaled(
    target: SparseRow,
    source: Mapping[int, Fraction],
    scale: Fraction,
) -> None:
    if not scale:
        return
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        elif column in target:
            del target[column]


def _build_extension_block(d: int) -> DecisionSystem:
    if (
        not isinstance(d, int)
        or isinstance(d, bool)
        or d not in {TRAINING_DIMENSION, CONDITIONAL_HOLDOUT_DIMENSION}
    ):
        raise ValueError("extension blocks are restricted to d=11 and d=12")
    compositions = tuple(sorted(support_compositions(d)))
    local_rows: dict[tuple[int, ...], SparseRow] = {
        composition: {} for composition in compositions
    }
    features = edge_features(d)
    for feature in features:
        edge_row = lifted_normalized_flow_row(feature)
        _add_scaled(local_rows[feature.parent], edge_row, feature.ratio)
        _add_scaled(local_rows[feature.child], edge_row, Fraction(-1))
    return DecisionSystem(
        dimensions=(d,),
        parameter_names=lifted_parameter_names(),
        row_labels=tuple((d, composition) for composition in compositions),
        rows=tuple(local_rows[composition] for composition in compositions),
        rhs=tuple(Fraction(s4(composition)) for composition in compositions),
        n_edges=len(features),
    )


def build_d11_block() -> DecisionSystem:
    return _build_extension_block(TRAINING_DIMENSION)


def build_cumulative_d11_system() -> DecisionSystem:
    blocks = tuple(build_dimension_system(d) for d in range(4, 11))
    return stack_systems(blocks + (build_d11_block(),))


def _prefix_d10_system() -> DecisionSystem:
    return stack_systems(
        tuple(build_dimension_system(d) for d in range(4, 11))
    )


def coefficient_echelon(system: DecisionSystem) -> CoefficientEchelon:
    """Return an exact deterministic echelon and canonical nullspace basis."""
    pivots: dict[int, SparseRow] = {}
    for source in system.rows:
        row = dict(source)
        while row:
            column = min(row)
            coefficient = row[column]
            if column in pivots:
                _add_scaled(row, pivots[column], -coefficient)
                continue
            reciprocal = Fraction(coefficient.denominator, coefficient.numerator)
            row = {key: value * reciprocal for key, value in row.items()}
            pivots[column] = row
            break
    n_parameters = len(system.parameter_names)
    pivot_columns = tuple(sorted(pivots))
    free_columns = tuple(
        column for column in range(n_parameters) if column not in pivots
    )
    basis = []
    for free_column in free_columns:
        vector = [Fraction(0) for _ in range(n_parameters)]
        vector[free_column] = Fraction(1)
        for pivot_column in reversed(pivot_columns):
            row = pivots[pivot_column]
            vector[pivot_column] = -sum(
                (
                    value * vector[column]
                    for column, value in row.items()
                    if column != pivot_column
                ),
                Fraction(0),
            )
        basis.append(tuple(vector))
    result = CoefficientEchelon(
        rank=len(pivots),
        pivot_columns=pivot_columns,
        free_columns=free_columns,
        nullspace_basis=tuple(basis),
    )
    verify_nullspace_basis(system, result)
    return result


def verify_nullspace_basis(
    system: DecisionSystem,
    echelon: CoefficientEchelon,
) -> dict[str, Any]:
    n_parameters = len(system.parameter_names)
    if len(echelon.nullspace_basis) != len(echelon.free_columns):
        raise AssertionError("nullspace basis has the wrong size")
    failures = 0
    coordinate_failures = 0
    for basis_index, (free_column, vector) in enumerate(
        zip(echelon.free_columns, echelon.nullspace_basis)
    ):
        if len(vector) != n_parameters:
            raise AssertionError("nullspace vector has the wrong width")
        if any(evaluate_sparse_row(row, vector) for row in system.rows):
            failures += 1
        for other_index, other_column in enumerate(echelon.free_columns):
            expected = Fraction(1) if other_index == basis_index else Fraction(0)
            if vector[other_column] != expected:
                coordinate_failures += 1
    result = {
        "verified": not failures and not coordinate_failures,
        "basis_size": len(echelon.nullspace_basis),
        "vector_width": n_parameters,
        "nonzero_residual_vectors": failures,
        "free_coordinate_failures": coordinate_failures,
    }
    if not result["verified"]:
        raise AssertionError("nullspace basis failed exact verification")
    return result


def _json_sha256(document: Any) -> str:
    encoded = json.dumps(
        document,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def coefficient_vector_hash(
    names: Sequence[str],
    coefficients: Sequence[Fraction],
) -> str:
    if len(names) != len(coefficients):
        raise ValueError("coefficient names and values have different lengths")
    return _json_sha256(
        {
            "parameter_names": list(names),
            "coefficients": [
                [str(value.numerator), str(value.denominator)]
                for value in map(Fraction, coefficients)
            ],
        }
    )


def _sparse_vector_document(
    names: Sequence[str],
    vector: Sequence[Fraction],
) -> list[dict[str, Any]]:
    return [
        {
            "column": column,
            "name": names[column],
            "value": fraction_record(value),
        }
        for column, value in enumerate(vector)
        if value
    ]


def _solution_document(
    system: DecisionSystem,
    coefficients: Sequence[Fraction],
) -> dict[str, Any]:
    verification = verify_solution(system, coefficients)
    if not verification["verified"]:
        raise AssertionError("saved coefficient vector has nonzero residual")
    return {
        "nonzero_coefficients": _sparse_vector_document(
            system.parameter_names, coefficients
        ),
        "coefficient_vector_sha256": coefficient_vector_hash(
            system.parameter_names, coefficients
        ),
        "verification": verification,
        "reconstructed_edge_verification": verify_reconstructed_divergence(
            system.dimensions, coefficients
        ),
    }


def verify_reconstructed_divergence(
    dimensions: Sequence[int],
    coefficients: Sequence[Fraction],
) -> dict[str, Any]:
    per_dimension = []
    total_edges = 0
    total_mismatches = 0
    for d in dimensions:
        divergence = {
            composition: Fraction(0) for composition in support_compositions(d)
        }
        features = edge_features(d)
        total_edges += len(features)
        for feature in features:
            normalized_flow = evaluate_sparse_row(
                lifted_normalized_flow_row(feature), coefficients
            )
            divergence[feature.parent] += feature.ratio * normalized_flow
            divergence[feature.child] -= normalized_flow
        mismatches = sum(
            divergence[composition] != Fraction(s4(composition))
            for composition in divergence
        )
        total_mismatches += mismatches
        per_dimension.append(
            {
                "d": d,
                "n_edges": len(features),
                "n_states": len(divergence),
                "n_mismatches": mismatches,
            }
        )
    result = {
        "verified": not total_mismatches,
        "n_edges": total_edges,
        "n_mismatches": total_mismatches,
        "per_dimension": per_dimension,
    }
    if not result["verified"]:
        raise AssertionError("reconstructed divergence verification failed")
    return result


def _conservation_relation(
    system: DecisionSystem,
    d: int,
) -> dict[str, Any]:
    indices = tuple(
        index for index, label in enumerate(system.row_labels) if label[0] == d
    )
    g_values = tuple(
        g_value(system.row_labels[index][1], d) for index in indices
    )
    divisor = reduce(gcd, g_values)
    multipliers = tuple(value // divisor for value in g_values)
    columns: SparseRow = {}
    target = Fraction(0)
    for row_index, multiplier in zip(indices, multipliers):
        _add_scaled(columns, system.rows[row_index], Fraction(multiplier))
        target += multiplier * system.rhs[row_index]
    if columns or target:
        raise AssertionError("structural conservation relation failed")
    return {
        "d": d,
        "support_size": len(indices),
        "G_common_divisor": str(divisor),
        "nonzero_column_sums": len(columns),
        "target_dot": fraction_record(target),
    }


def _structural_conservation_relations(
    system: DecisionSystem,
) -> list[dict[str, Any]]:
    return [_conservation_relation(system, d) for d in system.dimensions]


def _subsystem(system: DecisionSystem, indices: Sequence[int]) -> DecisionSystem:
    selected = tuple(indices)
    return DecisionSystem(
        dimensions=tuple(sorted({system.row_labels[index][0] for index in selected})),
        parameter_names=system.parameter_names,
        row_labels=tuple(system.row_labels[index] for index in selected),
        rows=tuple(system.rows[index] for index in selected),
        rhs=tuple(system.rhs[index] for index in selected),
        n_edges=system.n_edges,
    )


def _fundamental_witness(
    system: DecisionSystem,
    order: Sequence[int],
) -> dict[int, int]:
    reordered = _subsystem(system, order)
    elimination = exact_eliminate(reordered)
    if elimination.status != "inconsistent" or elimination.witness is None:
        raise AssertionError("inconsistent system produced no witness")
    local_witness, _ = primitive_integer_witness(
        elimination.witness, reordered.rhs
    )
    return {
        order[local_index]: multiplier
        for local_index, multiplier in local_witness.items()
        if multiplier
    }


def _exact_fundamental_circuit_search(
    system: DecisionSystem,
) -> tuple[dict[int, int], dict[str, Any]]:
    indices = tuple(range(len(system.rows)))
    orderings = {
        "canonical": indices,
        "reverse": tuple(reversed(indices)),
        "sparse_first": tuple(
            sorted(indices, key=lambda index: (len(system.rows[index]), index))
        ),
        "dense_first": tuple(
            sorted(indices, key=lambda index: (-len(system.rows[index]), index))
        ),
        "short_compositions_first": tuple(
            sorted(
                indices,
                key=lambda index: (
                    len(system.row_labels[index][1]),
                    system.row_labels[index][1],
                ),
            )
        ),
        "long_compositions_first": tuple(
            sorted(
                indices,
                key=lambda index: (
                    -len(system.row_labels[index][1]),
                    system.row_labels[index][1],
                ),
            )
        ),
    }
    candidates = []
    for name, order in orderings.items():
        witness = _fundamental_witness(system, order)
        support = tuple(sorted(witness))
        support_system = _subsystem(system, support)
        coefficient_rank, augmented_rank = system_ranks(support_system)
        is_circuit = (
            coefficient_rank == len(support) - 1
            and augmented_rank == len(support)
            and len(witness) == len(support)
        )
        if not is_circuit:
            raise AssertionError("fundamental witness did not form an exact circuit")
        candidates.append((len(support), name, witness))
    _, selected_name, selected_witness = min(
        candidates, key=lambda item: (item[0], item[1])
    )
    selected_support_size = len(selected_witness)
    return selected_witness, {
        "method": (
            "exact fundamental-circuit extraction under six deterministic "
            "row orderings; choose the smallest support"
        ),
        "candidate_support_sizes": {
            name: support_size for support_size, name, _ in sorted(candidates)
        },
        "selected_ordering": selected_name,
        "final_support_size": selected_support_size,
        "inclusion_minimal": True,
        "support_coefficient_rank": selected_support_size - 1,
        "support_augmented_rank": selected_support_size,
        "inclusion_minimality_certificate": (
            "on the selected support rank(A)=support_size-1 and "
            "rank([A|b])=support_size, so every proper row deletion is "
            "coefficient-independent and consistent"
        ),
        "minimum_cardinality_certified": False,
        "minimum_cardinality_note": (
            "global minimum-cardinality support was not searched; the saved "
            "support is exact and inclusion-minimal"
        ),
    }


def _inconsistency_document(
    cumulative_system: DecisionSystem,
    d11_block: DecisionSystem,
) -> dict[str, Any]:
    block_witness, minimization = _exact_fundamental_circuit_search(d11_block)
    row_offset = len(cumulative_system.rows) - len(d11_block.rows)
    witness = {
        row_offset + row_index: multiplier
        for row_index, multiplier in block_witness.items()
    }
    verification = verify_inconsistency_witness(cumulative_system, witness)
    if not verification["verified"]:
        raise AssertionError("inconsistency witness failed exact verification")
    primitive_gcd = reduce(gcd, (abs(value) for value in witness.values()))
    if primitive_gcd != 1:
        raise AssertionError("inconsistency witness is not primitive")
    if int(verification["rhs_dot"]["num"]) <= 0:
        raise AssertionError("inconsistency witness has the wrong orientation")
    rows = [
        {
            "row": row_index,
            "d": cumulative_system.row_labels[row_index][0],
            "composition": list(cumulative_system.row_labels[row_index][1]),
            "multiplier": str(multiplier),
        }
        for row_index, multiplier in sorted(witness.items())
        if multiplier
    ]
    return {
        "primitive_integer_multipliers": rows,
        "dimensions_present": sorted({row["d"] for row in rows}),
        "primitive_integer_normalization": {
            "gcd_of_absolute_multipliers": str(primitive_gcd),
            "orientation": "positive target pairing",
        },
        "verification": verification,
        "support_minimization": minimization,
        "relation_type": (
            "target-active non-conservation inconsistency relation: unlike "
            "every per-d global conservation relation, its target pairing "
            "is nonzero"
        ),
    }


def _nullspace_document(
    system: DecisionSystem,
    echelon: CoefficientEchelon,
) -> dict[str, Any]:
    verification = verify_nullspace_basis(system, echelon)
    vectors = []
    for free_column, vector in zip(
        echelon.free_columns, echelon.nullspace_basis
    ):
        vectors.append(
            {
                "free_column": free_column,
                "free_name": system.parameter_names[free_column],
                "vector_sha256": coefficient_vector_hash(
                    system.parameter_names, vector
                ),
                "nonzero_coefficients": _sparse_vector_document(
                    system.parameter_names, vector
                ),
            }
        )
    return {
        "basis_convention": (
            "one exact echelon vector per free column, with identity free "
            "coordinates and all other free coordinates zero"
        ),
        "pivot_columns": list(echelon.pivot_columns),
        "free_columns": list(echelon.free_columns),
        "vectors": vectors,
        "verification": verification,
        "basis_sha256": _json_sha256(vectors),
    }


def evaluate_strict_d12_holdout(
    frozen_coefficients: Sequence[Fraction],
) -> dict[str, Any]:
    """Evaluate d=12 without solving, refitting, or changing coefficients."""
    coefficients = tuple(Fraction(value) for value in frozen_coefficients)
    if len(coefficients) != PARAMETER_COUNT:
        raise ValueError("frozen vector must have 276 coefficients")
    block = _build_extension_block(CONDITIONAL_HOLDOUT_DIMENSION)
    residuals = []
    nonzero = []
    for row_index, ((d, composition), row, rhs) in enumerate(
        zip(block.row_labels, block.rows, block.rhs)
    ):
        residual = evaluate_sparse_row(row, coefficients) - rhs
        record = {
            "row": row_index,
            "d": d,
            "composition": list(composition),
            "residual": fraction_record(residual),
        }
        residuals.append(record)
        if residual:
            nonzero.append(record)
    return {
        "mode": "strict holdout evaluation of the frozen d<=11 vector; no refit",
        "n_rows": len(block.rows),
        "n_edges": block.n_edges,
        "residual_vector": residuals,
        "n_nonzero_residuals": len(nonzero),
        "first_violated_equation": nonzero[0] if nonzero else None,
        "nonzero_residual_support": nonzero,
        "all_equations_pass": not nonzero,
        "matrix_hashes": system_hashes(block),
    }


def run_d11_gate() -> dict[str, Any]:
    prefix_d10 = _prefix_d10_system()
    prefix_hashes = system_hashes(prefix_d10)
    if prefix_hashes != D10_HASHES:
        raise AssertionError("frozen d<=10 semantic or numerical hashes changed")
    d11_block = build_d11_block()
    d11_coefficient_rank, d11_augmented_rank = system_ranks(d11_block)
    raw = stack_systems(
        tuple(build_dimension_system(d) for d in range(4, 11))
        + (d11_block,)
    )
    deduplication = deduplicate_system(raw)
    system = deduplication.system
    coefficient_rank, augmented_rank = system_ranks(system)
    previous_rank = 217
    previous_nullity = 59
    new_constraints = coefficient_rank - previous_rank
    nullity = PARAMETER_COUNT - coefficient_rank
    raw_left_nullity = len(raw.rows) - coefficient_rank
    deduplicated_left_nullity = len(system.rows) - coefficient_rank
    result: dict[str, Any] = {
        "schema": GATE_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "scope": {
            "training_dimensions": list(range(4, 12)),
            "training_maximum_dimension": TRAINING_DIMENSION,
            "conditional_holdout_dimension": CONDITIONAL_HOLDOUT_DIMENSION,
            "parameter_count": PARAMETER_COUNT,
            "features_added_or_removed": False,
            "nonnegativity_optimization_run": False,
            "symbolic_extrapolation_run": False,
        },
        "frozen_d10_embedding": {
            "verified": True,
            "hashes": prefix_hashes,
        },
        "d11_block": {
            "raw_rows": len(d11_block.rows),
            "n_edges": d11_block.n_edges,
            "coefficient_rank": d11_coefficient_rank,
            "augmented_rank": d11_augmented_rank,
            "left_nullity": len(d11_block.rows) - d11_coefficient_rank,
            "augmented_left_nullity": (
                len(d11_block.rows) - d11_augmented_rank
            ),
            "equality_status": (
                "inconsistent"
                if d11_augmented_rank > d11_coefficient_rank
                else "consistent"
            ),
            "hashes": system_hashes(d11_block),
        },
        "cumulative_d11": {
            "raw_rows": len(raw.rows),
            "deduplicated_rows": len(system.rows),
            "duplicates_removed": len(raw.rows) - len(system.rows),
            "n_edges": raw.n_edges,
            "coefficient_rank": coefficient_rank,
            "augmented_rank": augmented_rank,
            "nullity": nullity,
            "raw_left_nullity": raw_left_nullity,
            "deduplicated_left_nullity": deduplicated_left_nullity,
            "augmented_left_nullity": len(raw.rows) - augmented_rank,
            "structural_conservation_dimension": len(raw.dimensions),
            "left_nullity_beyond_conservation": (
                raw_left_nullity - len(raw.dimensions)
            ),
            "compatible_nonconservation_left_nullity": (
                len(raw.rows) - augmented_rank - len(raw.dimensions)
            ),
            "target_active_left_relation_dimension": (
                augmented_rank - coefficient_rank
            ),
            "new_independent_constraints_from_d11": new_constraints,
            "previous_affine_dimension": previous_nullity,
            "coefficient_direction_dimension_reduction": (
                previous_nullity - nullity
            ),
            "affine_intersection": (
                "empty" if augmented_rank > coefficient_rank else "nonempty"
            ),
            "hashes": system_hashes(system),
        },
        "structural_conservation_relations": (
            _structural_conservation_relations(system)
        ),
    }
    if augmented_rank > coefficient_rank:
        result["decision_branch"] = "A_inconsistent"
        result["inconsistency_witness"] = _inconsistency_document(raw, d11_block)
        result["inconsistency_origin"] = (
            "a d=11-only inconsistency exists"
            if d11_augmented_rank > d11_coefficient_rank
            else (
                "the standalone d=11 block is consistent, so the obstruction "
                "is caused by requiring one coefficient vector jointly with "
                "the earlier dimensions"
            )
        )
        result["d12_constructed"] = False
        result["stopping_rule"] = (
            "stop immediately at the d<=11 equality inconsistency without "
            "feature repair or holdout construction"
        )
        return result

    elimination = exact_eliminate(system)
    if elimination.status != "consistent" or elimination.solution is None:
        raise AssertionError("equal ranks did not produce an exact solution")
    solution = tuple(elimination.solution)
    result["particular_solution"] = _solution_document(raw, solution)
    echelon = coefficient_echelon(system)
    if echelon.rank != coefficient_rank:
        raise AssertionError("coefficient echelon rank disagrees with scan rank")
    if coefficient_rank < PARAMETER_COUNT:
        result["decision_branch"] = "B_consistent_underdetermined"
        result["nullspace"] = _nullspace_document(system, echelon)
        result["d12_constructed"] = False
        result["stopping_rule"] = (
            "stop with the exact affine d<=11 solution space; do not choose "
            "a representative for holdout evaluation"
        )
        return result

    if coefficient_rank != PARAMETER_COUNT or echelon.free_columns:
        raise AssertionError("full-rank uniqueness check failed")
    result["decision_branch"] = "C_consistent_unique"
    result["unique_frozen_coefficient_vector"] = {
        "coefficient_vector_sha256": coefficient_vector_hash(
            raw.parameter_names, solution
        ),
        "coefficients": [fraction_record(value) for value in solution],
        "verification": result["particular_solution"]["verification"],
    }
    result["d12_constructed"] = True
    result["d12_strict_holdout"] = evaluate_strict_d12_holdout(solution)
    result["stopping_rule"] = (
        "stop after the strict d=12 evaluation of the frozen unique vector; "
        "do not refit, augment, or proceed to d=13"
    )
    return result


def _write_json(path: Path, document: Any) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    document = run_d11_gate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    _write_json(args.output, document)
    print(json.dumps(document, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
