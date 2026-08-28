"""Exact d=11 cokernel gate for the systematic weighted-degree-five lift.

Only new symbolic columns of exact weighted degree five are constructed.
The frozen 276 degree-at-most-four columns remain unchanged and first in the
extended ordering.  The decision is made in the nine-dimensional cokernel of
the standalone d=11 degree-four matrix; no full degree-five coefficient solve,
nonnegativity problem, or other dimension is constructed.
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
    PEEL_WIDTHS,
    Polynomial,
    balanced_invariant_basis,
    evaluate_polynomial,
    evaluate_sparse_row,
    exact_eliminate,
    fraction_record,
    matrix_rank,
    primitive_integer_witness,
    symmetry_basis,
    system_ranks,
    weighted_degree,
)
from k4_desymmetrized_d4 import (
    lifted_normalized_flow_row,
    lifted_parameter_names,
)
from k4_desymmetrized_d11_gate import (
    build_d11_block,
    coefficient_echelon,
)
from k4_desymmetrized_scan import system_hashes
from k4_feature_analysis import EdgeFeatures, edge_features, g_value


CHECKPOINT_BASE = "0b3603807fac8698e412053204e252cfe7da2c1c"
DIMENSION = 11
OLD_MAXIMUM_DEGREE = 4
NEW_MAXIMUM_DEGREE = 5
OLD_PARAMETER_COUNT = 276
GATE_SCHEMA = "chow-cone/k4-degree5-cokernel-gate/v1"
FROZEN_D11_HASHES = {
    "matrix_sha256": "f8f12e50980be7cd373291a670e3238513691d1e9735cebcc578f0bef28c36e4",
    "rhs_sha256": "80e85f7ab8850a099518736a85a9a508eab54d11f5c9d786c5a63ae5b7dbf070",
    "system_sha256": "205ece2143e69f67958dc73fc1fed0056be9440d3d9987b9a7b1906ac9e8665e",
}
SparseRow = dict[int, Fraction]


@dataclass(frozen=True)
class DegreeFiveFeature:
    name: str
    peel_width: int
    channel: str
    parity: str
    basis_index: int
    polynomial: Polynomial
    orientation_factor: int

    @property
    def oriented_polynomial(self) -> Polynomial:
        return tuple(
            (exponent, coefficient * self.orientation_factor)
            for exponent, coefficient in self.polynomial
        )

    @property
    def symbolic_key(self) -> tuple[Any, ...]:
        return self.peel_width, self.channel, self.oriented_polynomial

    def to_record(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "peel_width": self.peel_width,
            "channel": self.channel,
            "parity": self.parity,
            "basis_index": self.basis_index,
            "weighted_degree": NEW_MAXIMUM_DEGREE,
            "orientation_factor": self.orientation_factor,
            "polynomial": [
                {
                    "exponents": list(exponent),
                    "coefficient": coefficient,
                }
                for exponent, coefficient in self.polynomial
            ],
            "oriented_polynomial": [
                {
                    "exponents": list(exponent),
                    "coefficient": coefficient,
                }
                for exponent, coefficient in self.oriented_polynomial
            ],
        }


@dataclass(frozen=True)
class LeftKernelData:
    basis: tuple[tuple[int, ...], ...]
    free_row_indices: tuple[int, ...]
    conservation_replacement_index: int
    conservation_anchor_row: int


def _exact_degree_polynomials(
    polynomials: Sequence[Polynomial],
    degree: int,
) -> tuple[tuple[int, Polynomial], ...]:
    return tuple(
        (index, polynomial)
        for index, polynomial in enumerate(polynomials)
        if weighted_degree(polynomial[0][0]) == degree
    )


def degree_five_features() -> tuple[DegreeFiveFeature, ...]:
    """Return globally symbolically deduplicated exact-degree-five columns."""
    basis = symmetry_basis(NEW_MAXIMUM_DEGREE)
    balanced = balanced_invariant_basis(NEW_MAXIMUM_DEGREE)
    invariant = _exact_degree_polynomials(
        basis.invariant, NEW_MAXIMUM_DEGREE
    )
    anti = _exact_degree_polynomials(
        basis.anti_invariant, NEW_MAXIMUM_DEGREE
    )
    balanced_exact = _exact_degree_polynomials(
        balanced, NEW_MAXIMUM_DEGREE
    )
    candidates = []
    for peel in PEEL_WIDTHS:
        for channel in ("left", "right"):
            for index, polynomial in invariant:
                candidates.append(
                    DegreeFiveFeature(
                        name=f"s{peel}:{channel}:invariant:degree5:{index:02d}",
                        peel_width=peel,
                        channel=channel,
                        parity="invariant",
                        basis_index=index,
                        polynomial=polynomial,
                        orientation_factor=1,
                    )
                )
            anti_factor = 1 if channel == "left" else -1
            for index, polynomial in anti:
                candidates.append(
                    DegreeFiveFeature(
                        name=f"s{peel}:{channel}:anti:degree5:{index:02d}",
                        peel_width=peel,
                        channel=channel,
                        parity="anti",
                        basis_index=index,
                        polynomial=polynomial,
                        orientation_factor=anti_factor,
                    )
                )
        for index, polynomial in balanced_exact:
            candidates.append(
                DegreeFiveFeature(
                    name=f"s{peel}:balanced:invariant:degree5:{index:02d}",
                    peel_width=peel,
                    channel="balanced",
                    parity="invariant",
                    basis_index=index,
                    polynomial=polynomial,
                    orientation_factor=1,
                )
            )
    deduplicated: dict[tuple[Any, ...], DegreeFiveFeature] = {}
    for feature in candidates:
        deduplicated.setdefault(feature.symbolic_key, feature)
    result = tuple(deduplicated.values())
    if len(result) != len(candidates):
        raise AssertionError("unexpected duplicate exact-degree-five feature")
    if len({feature.name for feature in result}) != len(result):
        raise AssertionError("degree-five feature names are not unique")
    return result


def verify_feature_nesting() -> dict[str, Any]:
    old = symmetry_basis(OLD_MAXIMUM_DEGREE)
    new = symmetry_basis(NEW_MAXIMUM_DEGREE)
    old_balanced = balanced_invariant_basis(OLD_MAXIMUM_DEGREE)
    new_balanced = balanced_invariant_basis(NEW_MAXIMUM_DEGREE)
    invariant_prefix = tuple(
        polynomial
        for polynomial in new.invariant
        if weighted_degree(polynomial[0][0]) <= OLD_MAXIMUM_DEGREE
    )
    anti_prefix = tuple(
        polynomial
        for polynomial in new.anti_invariant
        if weighted_degree(polynomial[0][0]) <= OLD_MAXIMUM_DEGREE
    )
    balanced_prefix = tuple(
        polynomial
        for polynomial in new_balanced
        if weighted_degree(polynomial[0][0]) <= OLD_MAXIMUM_DEGREE
    )
    verified = (
        invariant_prefix == old.invariant
        and anti_prefix == old.anti_invariant
        and balanced_prefix == old_balanced
        and len(lifted_parameter_names()) == OLD_PARAMETER_COUNT
    )
    if not verified:
        raise AssertionError("degree-four symbolic basis did not embed unchanged")
    return {
        "verified": True,
        "old_parameters": OLD_PARAMETER_COUNT,
        "old_invariant_per_peel": len(old.invariant),
        "old_anti_per_peel": len(old.anti_invariant),
        "old_balanced_per_peel": len(old_balanced),
        "degree5_invariant_per_side_per_peel": len(
            _exact_degree_polynomials(new.invariant, NEW_MAXIMUM_DEGREE)
        ),
        "degree5_anti_per_side_per_peel": len(
            _exact_degree_polynomials(new.anti_invariant, NEW_MAXIMUM_DEGREE)
        ),
        "degree5_balanced_per_peel": len(
            _exact_degree_polynomials(new_balanced, NEW_MAXIMUM_DEGREE)
        ),
    }


def extended_parameter_names() -> tuple[str, ...]:
    return lifted_parameter_names() + tuple(
        feature.name for feature in degree_five_features()
    )


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


def degree_five_normalized_flow_row(feature: EdgeFeatures) -> SparseRow:
    values = _feature_values(feature)
    row: SparseRow = {}
    for column, symbolic in enumerate(degree_five_features()):
        if symbolic.peel_width != feature.peel_width:
            continue
        if symbolic.channel != feature.peel_side:
            continue
        value = symbolic.orientation_factor * evaluate_polynomial(
            symbolic.polynomial, values
        )
        if value:
            row[column] = Fraction(value)
    return row


def extended_normalized_flow_row(feature: EdgeFeatures) -> SparseRow:
    row = dict(lifted_normalized_flow_row(feature))
    for column, value in degree_five_normalized_flow_row(feature).items():
        row[OLD_PARAMETER_COUNT + column] = value
    return row


def verify_edgewise_old_embedding() -> dict[str, Any]:
    features = edge_features(DIMENSION)
    for feature in features:
        old = lifted_normalized_flow_row(feature)
        extended = extended_normalized_flow_row(feature)
        old_projection = {
            column: value
            for column, value in extended.items()
            if column < OLD_PARAMETER_COUNT
        }
        if old_projection != old:
            raise AssertionError("an old edge evaluator changed in the degree-five lift")
        if any(column < OLD_PARAMETER_COUNT for column in extended if column not in old):
            raise AssertionError("degree-five column entered the old coordinate block")
    names = extended_parameter_names()
    if names[:OLD_PARAMETER_COUNT] != lifted_parameter_names():
        raise AssertionError("the old parameter-name ordering changed")
    if set(names[:OLD_PARAMETER_COUNT]) & set(names[OLD_PARAMETER_COUNT:]):
        raise AssertionError("new degree-five names overlap old names")
    return {
        "verified": True,
        "d": DIMENSION,
        "n_edges_checked": len(features),
        "old_coordinate_count": OLD_PARAMETER_COUNT,
        "old_names_are_exact_prefix": True,
    }


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


def build_new_degree_five_matrix() -> DecisionSystem:
    """Build only the 144 x n_new exact-degree-five divergence block."""
    old = build_d11_block()
    local_rows: dict[tuple[int, ...], SparseRow] = {
        composition: {} for _, composition in old.row_labels
    }
    features = edge_features(DIMENSION)
    for feature in features:
        edge_row = degree_five_normalized_flow_row(feature)
        _add_scaled(local_rows[feature.parent], edge_row, feature.ratio)
        _add_scaled(local_rows[feature.child], edge_row, Fraction(-1))
    names = tuple(feature.name for feature in degree_five_features())
    return DecisionSystem(
        dimensions=(DIMENSION,),
        parameter_names=names,
        row_labels=old.row_labels,
        rows=tuple(
            local_rows[composition] for _, composition in old.row_labels
        ),
        rhs=tuple(Fraction(0) for _ in old.rows),
        n_edges=len(features),
    )


def _transpose_coefficient_system(system: DecisionSystem) -> DecisionSystem:
    n_original_rows = len(system.rows)
    transpose_rows = []
    for column in range(len(system.parameter_names)):
        transpose_rows.append(
            {
                row_index: row[column]
                for row_index, row in enumerate(system.rows)
                if column in row
            }
        )
    return DecisionSystem(
        dimensions=(DIMENSION,),
        parameter_names=tuple(
            f"state:{','.join(map(str, composition))}"
            for _, composition in system.row_labels
        ),
        row_labels=tuple((DIMENSION, (column,)) for column in range(len(transpose_rows))),
        rows=tuple(transpose_rows),
        rhs=tuple(Fraction(0) for _ in transpose_rows),
        n_edges=system.n_edges,
    )


def _lcm(first: int, second: int) -> int:
    if not first or not second:
        return 0
    return abs(first * second) // gcd(first, second)


def _primitive_integer_vector(values: Sequence[Fraction]) -> tuple[int, ...]:
    fractions = tuple(Fraction(value) for value in values)
    if not any(fractions):
        raise ValueError("cannot normalize the zero vector")
    denominator = reduce(
        _lcm,
        (value.denominator for value in fractions if value),
        1,
    )
    integers = tuple(
        value.numerator * (denominator // value.denominator)
        for value in fractions
    )
    divisor = reduce(gcd, (abs(value) for value in integers if value))
    primitive = tuple(value // divisor for value in integers)
    first = next(value for value in primitive if value)
    if first < 0:
        primitive = tuple(-value for value in primitive)
    return primitive


def left_kernel_data(old_system: DecisionSystem) -> LeftKernelData:
    """Return a primitive integer basis with conservation first."""
    transpose = _transpose_coefficient_system(old_system)
    echelon = coefficient_echelon(transpose)
    if echelon.rank != 135 or len(echelon.nullspace_basis) != 9:
        raise AssertionError("unexpected d=11 degree-four left-kernel dimension")
    conservation_values = tuple(
        g_value(composition, DIMENSION)
        for _, composition in old_system.row_labels
    )
    conservation = _primitive_integer_vector(conservation_values)
    replacement = next(
        index
        for index, free_column in enumerate(echelon.free_columns)
        if conservation[free_column]
    )
    basis = [conservation]
    basis.extend(
        _primitive_integer_vector(vector)
        for index, vector in enumerate(echelon.nullspace_basis)
        if index != replacement
    )
    result = tuple(basis)
    if len(result) != 9:
        raise AssertionError("conservation-first left-kernel basis has wrong size")
    if matrix_rank(
        tuple(
            {column: Fraction(value) for column, value in enumerate(vector) if value}
            for vector in result
        )
    ) != 9:
        raise AssertionError("conservation-first left-kernel basis is dependent")
    for vector in result:
        for column in range(len(old_system.parameter_names)):
            pairing = sum(
                Fraction(vector[row_index])
                * old_system.rows[row_index].get(column, Fraction(0))
                for row_index in range(len(old_system.rows))
            )
            if pairing:
                raise AssertionError("left-kernel vector does not annihilate A4")
    return LeftKernelData(
        basis=result,
        free_row_indices=echelon.free_columns,
        conservation_replacement_index=replacement,
        conservation_anchor_row=echelon.free_columns[replacement],
    )


def left_kernel_basis(old_system: DecisionSystem) -> tuple[tuple[int, ...], ...]:
    return left_kernel_data(old_system).basis


def _column_signatures(
    rows: Sequence[Mapping[int, Fraction]],
    n_columns: int,
    basis: Sequence[Sequence[int]],
) -> tuple[tuple[Fraction, ...], ...]:
    signatures = []
    for column in range(n_columns):
        signatures.append(
            tuple(
                sum(
                    Fraction(vector[row_index])
                    * rows[row_index].get(column, Fraction(0))
                    for row_index in range(len(rows))
                )
                for vector in basis
            )
        )
    return tuple(signatures)


def _target_signature(
    rhs: Sequence[Fraction],
    basis: Sequence[Sequence[int]],
) -> tuple[Fraction, ...]:
    return tuple(
        sum(
            Fraction(vector[row_index]) * rhs[row_index]
            for row_index in range(len(rhs))
        )
        for vector in basis
    )


def _signature_system(
    names: Sequence[str],
    signatures: Sequence[Sequence[Fraction]],
    target: Sequence[Fraction],
) -> DecisionSystem:
    rows = []
    for coordinate in range(len(target)):
        rows.append(
            {
                column: signature[coordinate]
                for column, signature in enumerate(signatures)
                if signature[coordinate]
            }
        )
    return DecisionSystem(
        dimensions=(DIMENSION,),
        parameter_names=tuple(names),
        row_labels=tuple((DIMENSION, (coordinate,)) for coordinate in range(len(target))),
        rows=tuple(rows),
        rhs=tuple(Fraction(value) for value in target),
        n_edges=0,
    )


def _fraction_list(values: Sequence[Fraction]) -> list[dict[str, str]]:
    return [fraction_record(value) for value in values]


def _json_sha256(document: Any) -> str:
    encoded = json.dumps(
        document,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _matrix_hash(rows: Sequence[Mapping[int, Fraction]], n_columns: int) -> str:
    return _json_sha256(
        {
            "n_rows": len(rows),
            "n_columns": n_columns,
            "rows": [
                [
                    [column, str(value.numerator), str(value.denominator)]
                    for column, value in sorted(row.items())
                ]
                for row in rows
            ],
        }
    )


def _verify_conservation_coordinate(
    signatures: Sequence[Sequence[Fraction]],
    target: Sequence[Fraction],
    old_system: DecisionSystem,
    conservation_vector: Sequence[int],
) -> dict[str, Any]:
    nonzero_columns = sum(bool(signature[0]) for signature in signatures)
    verified = not nonzero_columns and not target[0]
    if not verified:
        raise AssertionError("global conservation coordinate did not vanish")
    multiplier = {
        composition: conservation_vector[row_index]
        for row_index, (_, composition) in enumerate(old_system.row_labels)
    }
    edge_factor_failures = 0
    for feature in edge_features(DIMENSION):
        factor = (
            Fraction(multiplier[feature.parent]) * feature.ratio
            - Fraction(multiplier[feature.child])
        )
        if factor:
            edge_factor_failures += 1
    if edge_factor_failures:
        raise AssertionError("conservation failed on an individual legal edge")
    return {
        "verified": True,
        "legal_edges_checked": old_system.n_edges,
        "nonzero_edge_factors": edge_factor_failures,
        "new_columns_with_nonzero_conservation_coordinate": nonzero_columns,
        "target_conservation_coordinate": fraction_record(target[0]),
    }


def _combine_new_columns(
    new_matrix: DecisionSystem,
    coefficients: Mapping[int, Fraction],
) -> tuple[Fraction, ...]:
    return tuple(
        sum(
            row.get(column, Fraction(0)) * coefficient
            for column, coefficient in coefficients.items()
        )
        for row in new_matrix.rows
    )


def _restricted_signature_system(
    system: DecisionSystem,
    selected_columns: Sequence[int],
) -> DecisionSystem:
    selected = tuple(selected_columns)
    old_to_new = {column: index for index, column in enumerate(selected)}
    return DecisionSystem(
        dimensions=system.dimensions,
        parameter_names=tuple(system.parameter_names[column] for column in selected),
        row_labels=system.row_labels,
        rows=tuple(
            {
                old_to_new[column]: value
                for column, value in row.items()
                if column in old_to_new
            }
            for row in system.rows
        ),
        rhs=system.rhs,
        n_edges=0,
    )


def _inclusion_minimal_signature_solution(
    signature_system: DecisionSystem,
) -> tuple[dict[int, Fraction], dict[str, Any]]:
    initial = exact_eliminate(signature_system)
    if initial.status != "consistent" or initial.solution is None:
        raise ValueError("target signature is not in the new signature span")
    support = [
        column for column, value in enumerate(initial.solution) if value
    ]
    for candidate in tuple(reversed(support)):
        trial = tuple(column for column in support if column != candidate)
        if not trial:
            continue
        solved = exact_eliminate(_restricted_signature_system(signature_system, trial))
        if solved.status == "consistent":
            support = list(trial)
    final_system = _restricted_signature_system(signature_system, support)
    final = exact_eliminate(final_system)
    if final.status != "consistent" or final.solution is None:
        raise AssertionError("minimal signature support became inconsistent")
    coefficients = {
        support[index]: value
        for index, value in enumerate(final.solution)
        if value
    }
    if len(coefficients) != len(support):
        raise AssertionError("minimal signature representation has a zero coefficient")
    deletion_checks = []
    for candidate in support:
        trial = tuple(column for column in support if column != candidate)
        status = (
            "inconsistent"
            if not trial
            else exact_eliminate(
                _restricted_signature_system(signature_system, trial)
            ).status
        )
        deletion_checks.append({"column": candidate, "status": status})
        if status != "inconsistent":
            raise AssertionError("signature support is not inclusion-minimal")
    return coefficients, {
        "method": "exact reverse deletion from the canonical free-zero quotient solution",
        "support_size": len(coefficients),
        "inclusion_minimal": True,
        "minimum_cardinality_certified": False,
        "deletion_checks": deletion_checks,
    }


def _branch_a_witness(
    old_system: DecisionSystem,
    new_matrix: DecisionSystem,
    basis: Sequence[Sequence[int]],
    signature_system: DecisionSystem,
) -> dict[str, Any]:
    elimination = exact_eliminate(signature_system)
    if elimination.status != "inconsistent" or elimination.witness is None:
        raise AssertionError("signature obstruction produced no witness")
    coordinate_witness, _ = primitive_integer_witness(
        elimination.witness, signature_system.rhs
    )
    combined = tuple(
        sum(
            Fraction(multiplier) * Fraction(basis[coordinate][row_index])
            for coordinate, multiplier in coordinate_witness.items()
        )
        for row_index in range(len(old_system.rows))
    )
    primitive = _primitive_integer_vector(combined)
    initial_target_pairing = sum(
        Fraction(primitive[row_index]) * old_system.rhs[row_index]
        for row_index in range(len(old_system.rows))
    )
    if initial_target_pairing < 0:
        primitive = tuple(-value for value in primitive)
    old_nonzero = 0
    for column in range(len(old_system.parameter_names)):
        if sum(
            Fraction(primitive[row_index])
            * old_system.rows[row_index].get(column, Fraction(0))
            for row_index in range(len(old_system.rows))
        ):
            old_nonzero += 1
    new_nonzero = 0
    for column in range(len(new_matrix.parameter_names)):
        if sum(
            Fraction(primitive[row_index])
            * new_matrix.rows[row_index].get(column, Fraction(0))
            for row_index in range(len(new_matrix.rows))
        ):
            new_nonzero += 1
    target_pairing = sum(
        Fraction(primitive[row_index]) * old_system.rhs[row_index]
        for row_index in range(len(old_system.rows))
    )
    if old_nonzero or new_nonzero or not target_pairing:
        raise AssertionError("extended degree-five witness verification failed")
    return {
        "coordinate_multipliers": [
            {"coordinate": coordinate, "multiplier": str(multiplier)}
            for coordinate, multiplier in sorted(coordinate_witness.items())
            if multiplier
        ],
        "state_multipliers": [
            {
                "row": row_index,
                "composition": list(old_system.row_labels[row_index][1]),
                "multiplier": str(multiplier),
            }
            for row_index, multiplier in enumerate(primitive)
            if multiplier
        ],
        "primitive_gcd": str(
            reduce(gcd, (abs(value) for value in primitive if value))
        ),
        "verification": {
            "old_nonzero_column_pairings": old_nonzero,
            "new_nonzero_column_pairings": new_nonzero,
            "target_pairing": fraction_record(target_pairing),
            "verified": True,
        },
    }


def run_degree_five_quotient_gate() -> dict[str, Any]:
    nesting = verify_feature_nesting()
    edgewise_embedding = verify_edgewise_old_embedding()
    features = degree_five_features()
    old = build_d11_block()
    if system_hashes(old) != FROZEN_D11_HASHES:
        raise AssertionError("frozen degree-four d=11 matrix changed")
    if system_ranks(old) != (135, 136):
        raise AssertionError("frozen degree-four d=11 ranks changed")
    new_matrix = build_new_degree_five_matrix()
    if new_matrix.parameter_names != tuple(feature.name for feature in features):
        raise AssertionError("new feature and matrix order disagree")
    kernel = left_kernel_data(old)
    basis = kernel.basis
    signatures = _column_signatures(
        new_matrix.rows, len(features), basis
    )
    target = _target_signature(old.rhs, basis)
    conservation = _verify_conservation_coordinate(
        signatures, target, old, basis[0]
    )
    signature_system = _signature_system(
        new_matrix.parameter_names, signatures, target
    )
    signature_rank, augmented_signature_rank = system_ranks(signature_system)
    extended_rank = 135 + signature_rank
    feature_records = [feature.to_record() for feature in features]
    signature_records = [
        {
            "column": column,
            "name": features[column].name,
            "signature": _fraction_list(signature),
        }
        for column, signature in enumerate(signatures)
    ]
    result: dict[str, Any] = {
        "schema": GATE_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "scope": {
            "dimension": DIMENSION,
            "old_maximum_weighted_degree": OLD_MAXIMUM_DEGREE,
            "new_exact_weighted_degree": NEW_MAXIMUM_DEGREE,
            "full_degree5_coefficient_solve_run": False,
            "nonnegativity_optimization_run": False,
            "manual_features_added": [],
            "other_dimensions_constructed": False,
        },
        "frozen_degree4": {
            "parameter_count": len(old.parameter_names),
            "rank": 135,
            "hashes": FROZEN_D11_HASHES,
        },
        "feature_nesting": nesting,
        "edgewise_old_embedding": edgewise_embedding,
        "degree5_symbolic_columns": {
            "candidate_count": len(features),
            "globally_deduplicated_count": len(features),
            "duplicates_removed": 0,
            "extended_parameter_count": len(extended_parameter_names()),
            "definitions": feature_records,
            "definitions_sha256": _json_sha256(feature_records),
        },
        "d11_new_column_matrix": {
            "n_rows": len(new_matrix.rows),
            "n_columns": len(features),
            "matrix_sha256": _matrix_hash(new_matrix.rows, len(features)),
            "semantic_sha256": _json_sha256(
                {
                    "frozen_system_sha256": FROZEN_D11_HASHES["system_sha256"],
                    "row_labels": [
                        [d, list(composition)]
                        for d, composition in new_matrix.row_labels
                    ],
                    "ordered_feature_definitions": feature_records,
                    "matrix_sha256": _matrix_hash(
                        new_matrix.rows, len(features)
                    ),
                }
            ),
        },
        "left_kernel": {
            "dimension": len(basis),
            "conservation_coordinate": 0,
            "effective_obstruction_coordinates": list(range(1, len(basis))),
            "basis_vectors": [
                {
                    "coordinate": coordinate,
                    "role": (
                        "global_divergence_conservation"
                        if not coordinate
                        else "effective_obstruction_coordinate"
                    ),
                    "multipliers": [str(value) for value in vector],
                }
                for coordinate, vector in enumerate(basis)
            ],
            "free_row_indices": list(kernel.free_row_indices),
            "free_row_compositions": [
                list(old.row_labels[row_index][1])
                for row_index in kernel.free_row_indices
            ],
            "conservation_replacement_index": (
                kernel.conservation_replacement_index
            ),
            "conservation_anchor_row": kernel.conservation_anchor_row,
            "conservation_anchor_composition": list(
                old.row_labels[kernel.conservation_anchor_row][1]
            ),
            "direct_sum_description": (
                "Q*conservation plus the eight retained canonical kernel "
                "vectors vanishing at the conservation anchor row"
            ),
            "basis_rank": matrix_rank(
                tuple(
                    {
                        column: Fraction(value)
                        for column, value in enumerate(vector)
                        if value
                    }
                    for vector in basis
                )
            ),
            "basis_sha256": _json_sha256(basis),
            "conservation_verification": conservation,
        },
        "cokernel_signatures": {
            "target_signature": _fraction_list(target),
            "new_column_signatures": signature_records,
            "signatures_sha256": _json_sha256(signature_records),
            "new_signature_rank": signature_rank,
            "augmented_signature_rank": augmented_signature_rank,
            "evaluation_rank_modulo_old_columns": signature_rank,
            "zero_signature_count": sum(
                not any(signature) for signature in signatures
            ),
            "distinct_signature_count": len(set(signatures)),
            "coordinate_nonzero_column_counts": [
                sum(bool(signature[coordinate]) for signature in signatures)
                for coordinate in range(len(basis))
            ],
        },
        "enlarged_d11": {
            "parameter_count": len(extended_parameter_names()),
            "coefficient_rank": extended_rank,
            "nullity": len(extended_parameter_names()) - extended_rank,
            "rank_derivation": (
                "rank(A4) + rank of exact new-column cokernel signatures; "
                "no 144x524 elimination constructed"
            ),
        },
    }
    if augmented_signature_rank > signature_rank:
        result["decision_branch"] = "A_signature_not_spanned"
        result["enlarged_d11"]["augmented_rank"] = extended_rank + 1
        result["witness"] = _branch_a_witness(
            old, new_matrix, basis, signature_system
        )
        result["stopping_rule"] = (
            "the complete symbolic degree<=5 class is inconsistent at d=11; "
            "stop without feature repair or a full coefficient solve"
        )
        return result

    coefficients, minimization = _inclusion_minimal_signature_solution(
        signature_system
    )
    combination = _combine_new_columns(new_matrix, coefficients)
    residual = tuple(
        old.rhs[row_index] - combination[row_index]
        for row_index in range(len(old.rows))
    )
    residual_signature = _target_signature(residual, basis)
    if any(residual_signature):
        raise AssertionError("quotient solution left a nonzero cokernel residual")
    residual_system = DecisionSystem(
        dimensions=(DIMENSION,),
        parameter_names=old.parameter_names,
        row_labels=old.row_labels,
        rows=old.rows,
        rhs=residual,
        n_edges=old.n_edges,
    )
    residual_ranks = system_ranks(residual_system)
    if residual_ranks != (135, 135):
        raise AssertionError("degree-five corrected target is not in col(A4)")
    result["decision_branch"] = "B_signature_spanned"
    result["enlarged_d11"]["augmented_rank"] = extended_rank
    result["minimal_signature_certificate"] = {
        "columns": [
            {
                "column": column,
                "coefficient": fraction_record(value),
                "feature": features[column].to_record(),
                "signature": _fraction_list(signatures[column]),
            }
            for column, value in sorted(coefficients.items())
        ],
        "support_minimization": minimization,
        "target_signature_reproduced": True,
        "corrected_target_signature": _fraction_list(residual_signature),
        "corrected_target_old_matrix_ranks": {
            "coefficient_rank": residual_ranks[0],
            "augmented_rank": residual_ranks[1],
        },
    }
    result["stopping_rule"] = (
        "stop after the exact d=11 quotient certificate; do not compute a "
        "full coefficient vector or evaluate any other dimension"
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
    document = run_degree_five_quotient_gate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    _write_json(args.output, document)
    print(json.dumps(document, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
