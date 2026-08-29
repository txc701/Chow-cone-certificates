"""Exact shared-coefficient degree-five equality gate for d=2,...,11.

The 524 columns are the dimension-independent symbolic columns frozen in the
degree-five quotient checkpoint: the 276 desymmetrized weighted-degree-at-most
four columns followed by the 248 exact weighted-degree-five columns.  This
module substitutes that one coefficient vector into every divergence equation
for d=2,...,11.  Equality consistency is decided independently of edge-flow
nonnegativity.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
from math import gcd
import hashlib
import json
from pathlib import Path
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from k4_degree4_decision import (
    DecisionSystem,
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
)
from k4_degree5_quotient_gate import (
    OLD_PARAMETER_COUNT,
    degree_five_features,
    extended_normalized_flow_row,
    extended_parameter_names,
)
from k4_desymmetrized_d11_gate import coefficient_echelon
from k4_desymmetrized_d4 import (
    lifted_normalized_flow_row,
    lifted_parameter_names,
)
from k4_desymmetrized_scan import stack_systems, system_hashes
from k4_feature_analysis import EdgeFeatures, edge_features, g_value
from k4_weights import s4
from support import support_compositions


MINIMUM_DIMENSION = 2
MAXIMUM_DIMENSION = 11
PARAMETER_COUNT = 524
SparseRow = dict[int, Fraction]
RationalPolynomial = tuple[tuple[tuple[int, ...], Fraction], ...]


@dataclass(frozen=True)
class AffineDecomposition:
    """Exact coefficient/edge quotient decomposition of the solution space."""

    edge_rank: int
    edge_pivot_columns: tuple[int, ...]
    edge_free_columns: tuple[int, ...]
    edge_invisible_basis: tuple[tuple[Fraction, ...], ...]
    particular_solution: tuple[Fraction, ...]
    flow_kernel_basis: tuple[tuple[Fraction, ...], ...]


def _json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _fraction_pair(value: Fraction) -> list[str]:
    value = Fraction(value)
    return [str(value.numerator), str(value.denominator)]


def _sparse_vector(vector: Sequence[Fraction]) -> list[list[str | int]]:
    return [
        [column, str(value.numerator), str(value.denominator)]
        for column, value in enumerate(map(Fraction, vector))
        if value
    ]


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


def build_dimension_system(d: int) -> DecisionSystem:
    """Build one exact 524-column divergence block."""
    if not isinstance(d, int) or isinstance(d, bool):
        raise ValueError("dimension must be an integer")
    if not MINIMUM_DIMENSION <= d <= MAXIMUM_DIMENSION:
        raise ValueError("dimension must lie between 2 and 11")
    compositions = tuple(sorted(support_compositions(d)))
    local_rows: dict[tuple[int, ...], SparseRow] = {
        composition: {} for composition in compositions
    }
    features = edge_features(d)
    for feature in features:
        edge_row = extended_normalized_flow_row(feature)
        _add_scaled(local_rows[feature.parent], edge_row, feature.ratio)
        _add_scaled(local_rows[feature.child], edge_row, Fraction(-1))
    names = extended_parameter_names()
    if len(names) != PARAMETER_COUNT:
        raise AssertionError("unexpected degree-five parameter count")
    return DecisionSystem(
        dimensions=(d,),
        parameter_names=names,
        row_labels=tuple((d, composition) for composition in compositions),
        rows=tuple(local_rows[composition] for composition in compositions),
        rhs=tuple(Fraction(s4(composition)) for composition in compositions),
        n_edges=len(features),
    )


def build_cumulative_system(
    maximum_dimension: int = MAXIMUM_DIMENSION,
) -> DecisionSystem:
    if not MINIMUM_DIMENSION <= maximum_dimension <= MAXIMUM_DIMENSION:
        raise ValueError("maximum dimension must lie between 2 and 11")
    return stack_systems(
        tuple(
            build_dimension_system(d)
            for d in range(MINIMUM_DIMENSION, maximum_dimension + 1)
        )
    )


def build_edge_evaluation_system() -> DecisionSystem:
    """Return E, the exact normalized edge-evaluation map for d=2,...,11."""
    names = extended_parameter_names()
    rows = []
    labels = []
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        for edge_index, feature in enumerate(edge_features(d)):
            rows.append(extended_normalized_flow_row(feature))
            labels.append((d, (edge_index,)))
    return DecisionSystem(
        dimensions=tuple(range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1)),
        parameter_names=names,
        row_labels=tuple(labels),
        rows=tuple(rows),
        rhs=tuple(Fraction(0) for _ in rows),
        n_edges=len(rows),
    )


def restrict_columns(
    system: DecisionSystem,
    retained_columns: Sequence[int],
) -> DecisionSystem:
    """Restrict a system to an ordered set of distinct columns."""
    retained = tuple(retained_columns)
    if len(set(retained)) != len(retained):
        raise ValueError("retained columns must be distinct")
    if any(
        not isinstance(column, int)
        or isinstance(column, bool)
        or not 0 <= column < len(system.parameter_names)
        for column in retained
    ):
        raise ValueError("retained column is out of range")
    new_index = {column: index for index, column in enumerate(retained)}
    return DecisionSystem(
        dimensions=system.dimensions,
        parameter_names=tuple(system.parameter_names[column] for column in retained),
        row_labels=system.row_labels,
        rows=tuple(
            {
                new_index[column]: value
                for column, value in row.items()
                if column in new_index
            }
            for row in system.rows
        ),
        rhs=system.rhs,
        n_edges=system.n_edges,
    )


def _lift_vector(
    vector: Sequence[Fraction],
    retained_columns: Sequence[int],
    full_width: int,
) -> tuple[Fraction, ...]:
    if len(vector) != len(retained_columns):
        raise ValueError("vector and retained columns have different lengths")
    lifted = [Fraction(0) for _ in range(full_width)]
    for column, value in zip(retained_columns, vector):
        lifted[column] = Fraction(value)
    return tuple(lifted)


def affine_decomposition() -> AffineDecomposition:
    """Split ker(A) into edge-invisible and divergence-free-flow directions.

    The deterministic min-column echelon of E supplies a 407-column section
    of coefficient space modulo ker(E).  Restricting A to that section leaves
    a 47-dimensional homogeneous space of evaluated divergence-free flows.
    """
    edge_system = build_edge_evaluation_system()
    edge_echelon = coefficient_echelon(edge_system)
    cumulative = build_cumulative_system()
    section = restrict_columns(cumulative, edge_echelon.pivot_columns)
    elimination = exact_eliminate(section)
    if elimination.status != "consistent" or elimination.solution is None:
        raise AssertionError("edge-identifiable equality section is inconsistent")
    section_echelon = coefficient_echelon(section)
    full_width = len(cumulative.parameter_names)
    particular = _lift_vector(
        elimination.solution, edge_echelon.pivot_columns, full_width
    )
    flow_kernel = tuple(
        _lift_vector(vector, edge_echelon.pivot_columns, full_width)
        for vector in section_echelon.nullspace_basis
    )
    if any(
        evaluate_sparse_row(row, particular) != rhs
        for row, rhs in zip(cumulative.rows, cumulative.rhs)
    ):
        raise AssertionError("lifted particular solution has nonzero residual")
    if any(
        evaluate_sparse_row(row, vector)
        for vector in flow_kernel
        for row in cumulative.rows
    ):
        raise AssertionError("lifted flow-kernel direction has nonzero divergence")
    if any(
        evaluate_sparse_row(row, vector)
        for vector in edge_echelon.nullspace_basis
        for row in edge_system.rows
    ):
        raise AssertionError("edge-invisible direction changed an edge value")
    if (
        len(edge_echelon.nullspace_basis) + len(flow_kernel)
        != PARAMETER_COUNT - section_echelon.rank
    ):
        raise AssertionError("homogeneous direct-sum dimension mismatch")
    return AffineDecomposition(
        edge_rank=edge_echelon.rank,
        edge_pivot_columns=edge_echelon.pivot_columns,
        edge_free_columns=edge_echelon.free_columns,
        edge_invisible_basis=edge_echelon.nullspace_basis,
        particular_solution=particular,
        flow_kernel_basis=flow_kernel,
    )


def _scaled_polynomial(
    polynomial: Polynomial,
    scale: Fraction,
) -> tuple[tuple[tuple[int, ...], Fraction], ...]:
    return tuple(
        (exponent, scale * coefficient)
        for exponent, coefficient in polynomial
    )


def _add_polynomial_terms(
    target: dict[tuple[int, ...], Fraction],
    polynomial: Sequence[tuple[tuple[int, ...], Fraction]],
) -> None:
    for exponent, coefficient in polynomial:
        updated = target.get(exponent, Fraction(0)) + coefficient
        if updated:
            target[exponent] = updated
        elif exponent in target:
            del target[exponent]


def channel_polynomials(
    coefficients: Sequence[Fraction],
) -> dict[str, RationalPolynomial]:
    """Expand one coefficient vector into its six raw channel polynomials."""
    values = tuple(map(Fraction, coefficients))
    names = extended_parameter_names()
    if len(values) != len(names):
        raise ValueError("coefficient vector has the wrong length")
    accumulators: dict[str, dict[tuple[int, ...], Fraction]] = {
        f"s{peel}:{channel}": {}
        for peel in (2, 3)
        for channel in ("left", "right", "balanced")
    }
    basis = symmetry_basis(4)
    balanced = balanced_invariant_basis(4)
    for column, name in enumerate(lifted_parameter_names()):
        value = values[column]
        if not value:
            continue
        fields = name.split(":")
        peel = int(fields[0][1:])
        channel = fields[1]
        parity = fields[2]
        index = int(fields[3])
        if channel == "balanced":
            polynomial = balanced[index]
            orientation = 1
        elif parity == "invariant":
            polynomial = basis.invariant[index]
            orientation = 1
        elif parity == "anti":
            polynomial = basis.anti_invariant[index]
            orientation = -1 if channel == "right" else 1
        else:
            raise AssertionError("unknown old feature kind")
        _add_polynomial_terms(
            accumulators[f"s{peel}:{channel}"],
            _scaled_polynomial(polynomial, value * orientation),
        )
    for offset, feature in enumerate(degree_five_features()):
        value = values[OLD_PARAMETER_COUNT + offset]
        if not value:
            continue
        _add_polynomial_terms(
            accumulators[f"s{feature.peel_width}:{feature.channel}"],
            _scaled_polynomial(feature.polynomial, value * feature.orientation_factor),
        )
    return {
        channel: tuple(sorted(polynomial.items()))
        for channel, polynomial in accumulators.items()
    }


def evaluate_channel_polynomial(
    feature: EdgeFeatures,
    polynomials: Mapping[str, RationalPolynomial],
) -> Fraction:
    channel = f"s{feature.peel_width}:{feature.peel_side}"
    values = (
        feature.z,
        feature.L,
        feature.R,
        feature.VL,
        feature.VR,
        feature.QL,
        feature.QR,
    )
    return sum(
        (
            coefficient
            * evaluate_polynomial(((exponent, 1),), values)
            for exponent, coefficient in polynomials[channel]
        ),
        Fraction(0),
    )


def verify_channel_export(
    coefficients: Sequence[Fraction],
) -> dict[str, Any]:
    polynomials = channel_polynomials(coefficients)
    mismatches = 0
    checked = 0
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        for feature in edge_features(d):
            checked += 1
            expected = evaluate_sparse_row(
                extended_normalized_flow_row(feature), coefficients
            )
            actual = evaluate_channel_polynomial(feature, polynomials)
            if actual != expected:
                mismatches += 1
    result = {
        "verified": mismatches == 0,
        "edges_checked": checked,
        "mismatches": mismatches,
        "monomial_counts": {
            channel: len(polynomial)
            for channel, polynomial in polynomials.items()
        },
    }
    if not result["verified"]:
        raise AssertionError("symbolic channel export changed an edge value")
    return result


def _polynomial_document(
    polynomials: Mapping[str, RationalPolynomial],
) -> dict[str, list[dict[str, Any]]]:
    return {
        channel: [
            {
                "exponents": list(exponent),
                "coefficient": _fraction_pair(coefficient),
            }
            for exponent, coefficient in polynomial
        ]
        for channel, polynomial in polynomials.items()
    }


def candidate_edge_representation_system() -> DecisionSystem:
    """Ask whether the uniform rerouted flow lies in the tested feature image."""
    from k4_uniform_certificate import candidate_flow

    edge_system = build_edge_evaluation_system()
    rhs = []
    labels = []
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        raw_flow = candidate_flow(d)
        for edge_index, feature in enumerate(edge_features(d)):
            rhs.append(Fraction(raw_flow.get(feature.edge, 0), feature.G_child))
            labels.append((d, (edge_index,)))
    return DecisionSystem(
        dimensions=edge_system.dimensions,
        parameter_names=edge_system.parameter_names,
        row_labels=tuple(labels),
        rows=edge_system.rows,
        rhs=tuple(rhs),
        n_edges=edge_system.n_edges,
    )


def affine_space_document() -> tuple[dict[str, Any], dict[str, Any]]:
    """Return exact decision and full direct-sum affine-space artifacts."""
    uniformity = verify_symbolic_uniformity()
    cumulative = build_cumulative_system()
    ranks = system_ranks(cumulative)
    if ranks != (360, 360):
        raise AssertionError("unexpected cumulative degree-five ranks")
    decomposition = affine_decomposition()
    particular_verification = verify_reconstructed_divergence(
        decomposition.particular_solution
    )
    channel_verification = verify_channel_export(
        decomposition.particular_solution
    )
    edge_system = build_edge_evaluation_system()
    edge_values = tuple(
        evaluate_sparse_row(row, decomposition.particular_solution)
        for row in edge_system.rows
    )
    polynomials = channel_polynomials(decomposition.particular_solution)
    representation = candidate_edge_representation_system()
    representation_ranks = system_ranks(representation)
    if representation_ranks != (407, 408):
        raise AssertionError("unexpected uniform-flow representation ranks")
    representation_elimination = exact_eliminate(representation)
    if (
        representation_elimination.status != "inconsistent"
        or representation_elimination.witness is None
    ):
        raise AssertionError("uniform flow unexpectedly entered feature image")
    representation_witness, representation_pairing = primitive_integer_witness(
        representation_elimination.witness, representation.rhs
    )
    representation_verification = verify_integer_witness(
        representation, representation_witness
    )
    if not representation_verification["verified"]:
        raise AssertionError("edge-representation witness failed")
    ordered_edge_features = tuple(
        feature
        for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1)
        for feature in edge_features(d)
    )
    invisible = [_sparse_vector(vector) for vector in decomposition.edge_invisible_basis]
    flow_kernel = [_sparse_vector(vector) for vector in decomposition.flow_kernel_basis]
    particular = _sparse_vector(decomposition.particular_solution)
    affine = {
        "schema": "chow-cone/k4-degree5-uniform-affine-space/v1",
        "parameter_names": list(cumulative.parameter_names),
        "particular_solution": particular,
        "edge_invisible_basis": invisible,
        "divergence_free_flow_basis": flow_kernel,
        "coordinate_convention": (
            "deterministic min-column echelon; the particular solution is "
            "zero on the 47 free coordinates of A restricted to the 407 "
            "edge-pivot columns"
        ),
        "hashes": {
            "particular_solution_sha256": _json_sha256(particular),
            "edge_invisible_basis_sha256": _json_sha256(invisible),
            "divergence_free_flow_basis_sha256": _json_sha256(flow_kernel),
        },
    }
    decision = {
        "schema": "chow-cone/k4-degree5-shared-equality/v1",
        "scope": {
            "dimensions": list(cumulative.dimensions),
            "one_shared_coefficient_vector": True,
            "nonnegativity_of_entire_affine_family_decided": False,
            "finite_testing_is_not_an_all_d_proof": True,
        },
        "symbolic_uniformity": uniformity,
        "cumulative_system": {
            "rows": len(cumulative.rows),
            "columns": len(cumulative.parameter_names),
            "edges": cumulative.n_edges,
            "coefficient_rank": ranks[0],
            "augmented_rank": ranks[1],
            "nullity": PARAMETER_COUNT - ranks[0],
            "hashes": system_hashes(cumulative),
        },
        "affine_decomposition": {
            "edge_evaluation_rank": decomposition.edge_rank,
            "edge_invisible_dimension": len(decomposition.edge_invisible_basis),
            "divergence_free_evaluated_flow_dimension": len(
                decomposition.flow_kernel_basis
            ),
            "total_homogeneous_dimension": (
                len(decomposition.edge_invisible_basis)
                + len(decomposition.flow_kernel_basis)
            ),
            "edge_pivot_columns": list(decomposition.edge_pivot_columns),
            "edge_free_columns": list(decomposition.edge_free_columns),
            "particular_nonzero_coefficients": len(particular),
            "particular_edge_signs": {
                "negative": sum(value < 0 for value in edge_values),
                "zero": sum(value == 0 for value in edge_values),
                "positive": sum(value > 0 for value in edge_values),
            },
            "particular_verification": particular_verification,
            "channel_polynomial_verification": channel_verification,
        },
        "canonical_channel_polynomials": _polynomial_document(polynomials),
        "uniform_certificate_relation": {
            "candidate_is_in_degree5_feature_image": False,
            "coefficient_rank": representation_ranks[0],
            "augmented_rank": representation_ranks[1],
            "primitive_witness_support": len(representation_witness),
            "primitive_witness_target_pairing": representation_pairing,
            "witness": [
                {
                    "row": row,
                    "d": representation.row_labels[row][0],
                    "edge_index": representation.row_labels[row][1][0],
                    "parent": list(ordered_edge_features[row].parent),
                    "block_index": ordered_edge_features[row].block_index,
                    "split": ordered_edge_features[row].left_part,
                    "child": list(ordered_edge_features[row].child),
                    "candidate_normalized_flow": _fraction_pair(
                        representation.rhs[row]
                    ),
                    "multiplier": multiplier,
                }
                for row, multiplier in sorted(representation_witness.items())
            ],
            "verification": representation_verification,
            "interpretation": (
                "already at d=4 the candidate normalized flows are 360 and "
                "144 on the reversed balanced edges (2,4)->(2,2,2) and "
                "(4,2)->(2,2,2), whereas every current balanced column is "
                "mirror-invariant and evaluates equally on that pair; this "
                "obstructs representation of this candidate only and does not "
                "decide whether another nonnegative point lies in the "
                "164-dimensional finite-training affine family"
            ),
        },
    }
    return decision, affine


def verify_symbolic_uniformity() -> dict[str, Any]:
    """Verify one ordered symbolic definition evaluates in every dimension."""
    names = extended_parameter_names()
    old_names = lifted_parameter_names()
    new_features = degree_five_features()
    if names[:OLD_PARAMETER_COUNT] != old_names:
        raise AssertionError("old 276 columns are not the unchanged prefix")
    if names[OLD_PARAMETER_COUNT:] != tuple(
        feature.name for feature in new_features
    ):
        raise AssertionError("degree-five names do not match symbolic features")
    edge_count = 0
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        for feature in edge_features(d):
            edge_count += 1
            old = lifted_normalized_flow_row(feature)
            extended = extended_normalized_flow_row(feature)
            projection = {
                column: value
                for column, value in extended.items()
                if column < OLD_PARAMETER_COUNT
            }
            if projection != old:
                raise AssertionError("old edge evaluator changed")
            if any(column >= len(names) for column in extended):
                raise AssertionError("edge evaluator used an unknown column")
    return {
        "verified": True,
        "dimensions": list(range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1)),
        "edges_checked": edge_count,
        "old_parameter_count": OLD_PARAMETER_COUNT,
        "new_parameter_count": len(new_features),
        "total_parameter_count": len(names),
        "old_columns_are_exact_prefix": True,
    }


def verify_reconstructed_divergence(
    coefficients: Sequence[Fraction],
) -> dict[str, Any]:
    if len(coefficients) != PARAMETER_COUNT:
        raise ValueError("coefficient vector has the wrong length")
    per_dimension = []
    mismatch_count = 0
    edge_count = 0
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        divergence = {
            composition: Fraction(0) for composition in support_compositions(d)
        }
        features = edge_features(d)
        edge_count += len(features)
        for feature in features:
            normalized = evaluate_sparse_row(
                extended_normalized_flow_row(feature), coefficients
            )
            divergence[feature.parent] += feature.ratio * normalized
            divergence[feature.child] -= normalized
        mismatches = [
            composition
            for composition, value in divergence.items()
            if value != Fraction(s4(composition))
        ]
        mismatch_count += len(mismatches)
        per_dimension.append(
            {
                "d": d,
                "states": len(divergence),
                "edges": len(features),
                "mismatches": len(mismatches),
            }
        )
    return {
        "verified": mismatch_count == 0,
        "edges_checked": edge_count,
        "mismatches": mismatch_count,
        "per_dimension": per_dimension,
    }


def verify_integer_witness(
    system: DecisionSystem,
    witness: Mapping[int, int],
) -> dict[str, Any]:
    column_sum: SparseRow = {}
    target_sum = Fraction(0)
    for row_index, multiplier in witness.items():
        _add_scaled(column_sum, system.rows[row_index], Fraction(multiplier))
        target_sum += multiplier * system.rhs[row_index]
    return {
        "verified": not column_sum and bool(target_sum),
        "support_size": len(witness),
        "nonzero_column_pairings": len(column_sum),
        "target_pairing": fraction_record(target_sum),
    }


def primitive_inconsistency_witness(
    system: DecisionSystem,
) -> tuple[dict[int, int], dict[str, Any]]:
    elimination = exact_eliminate(system)
    if elimination.status != "inconsistent" or elimination.witness is None:
        raise ValueError("system is not inconsistent")
    primitive, pairing = primitive_integer_witness(
        elimination.witness, system.rhs
    )
    verification = verify_integer_witness(system, primitive)
    if not verification["verified"]:
        raise AssertionError("primitive witness failed exact verification")
    rows = [
        {
            "row": row,
            "d": system.row_labels[row][0],
            "composition": list(system.row_labels[row][1]),
            "multiplier": multiplier,
        }
        for row, multiplier in sorted(primitive.items())
    ]
    return primitive, {
        "primitive": reduce(gcd, (abs(value) for value in primitive.values())) == 1,
        "target_pairing": pairing,
        "rows": rows,
        "dimensions": sorted({row["d"] for row in rows}),
        "verification": verification,
    }


def run_gate() -> dict[str, Any]:
    uniformity = verify_symbolic_uniformity()
    system = build_cumulative_system()
    coefficient_rank, augmented_rank = system_ranks(system)
    result: dict[str, Any] = {
        "scope": {
            "dimensions": list(system.dimensions),
            "equality_only": True,
            "nonnegativity_tested": False,
        },
        "symbolic_uniformity": uniformity,
        "system": {
            "rows": len(system.rows),
            "columns": len(system.parameter_names),
            "edges": system.n_edges,
            "coefficient_rank": coefficient_rank,
            "augmented_rank": augmented_rank,
            "nullity": len(system.parameter_names) - coefficient_rank,
        },
    }
    if augmented_rank > coefficient_rank:
        _, witness = primitive_inconsistency_witness(system)
        result["decision"] = "inconsistent"
        result["witness"] = witness
        return result
    elimination = exact_eliminate(system)
    if elimination.status != "consistent" or elimination.solution is None:
        raise AssertionError("consistent ranks but elimination failed")
    verification = verify_reconstructed_divergence(elimination.solution)
    if not verification["verified"]:
        raise AssertionError("solution failed edgewise reconstruction")
    echelon = coefficient_echelon(system)
    result["decision"] = "consistent"
    result["solution"] = {
        "nonzero_count": sum(bool(value) for value in elimination.solution),
        "verification": verification,
        "homogeneous_dimension": len(echelon.nullspace_basis),
    }
    return result


def _write_json(path: Path, document: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args(argv)
    decision, affine = affine_space_document()
    _write_json(args.output_dir.joinpath("decision.json"), decision)
    _write_json(args.output_dir.joinpath("affine_space.json"), affine)
    print(json.dumps(decision, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
