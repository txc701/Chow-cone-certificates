"""Exact decision problem for the complete weighted-degree-four k=4 ansatz.

This module never reads a saved max-flow certificate.  It constructs a fixed
dimension-independent polynomial ansatz for the normalized edge flow

    h(parent -> child) = f(parent -> child) / G(child)

and substitutes it directly into the exact divergence equations

    sum_out (G(child) / G(parent)) h - sum_in h = S4(parent).

The feature mirror is composition reversal.  It is an involution of the
support split graph, but the distinguished final block in G means it is not a
symmetry of the divergence operator.  Mirror equivariance is therefore an
explicit restriction of the ansatz tested here, not a property inferred from
arbitrary feasible flows.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import gcd
from typing import Any, Iterable, Mapping, Sequence

from k4_feature_analysis import EdgeFeatures, edge_features
from k4_weights import s4
from support import support_compositions


BASIS_SCHEMA = "chow-cone/k4-degree4-basis/v1"
SYSTEM_SCHEMA = "chow-cone/k4-degree4-training-system/v1"
WITNESS_SCHEMA = "chow-cone/k4-degree4-inconsistency-witness/v1"
SOLUTION_SCHEMA = "chow-cone/k4-degree4-prefix-solution/v1"
RESULT_SCHEMA = "chow-cone/k4-degree4-decision/v1"

TRAINING_DIMENSIONS = tuple(range(2, 13))
HOLDOUT_DIMENSIONS = tuple(range(13, 17))
PEEL_WIDTHS = (2, 3)

VARIABLE_NAMES = ("z", "L", "R", "VL", "VR", "QL", "QR")
VARIABLE_WEIGHTS = (1, 1, 1, 2, 2, 4, 4)
MIRROR_VARIABLE_INDEX = (0, 2, 1, 4, 3, 6, 5)

Exponent = tuple[int, ...]
Polynomial = tuple[tuple[Exponent, int], ...]
SparseRow = dict[int, Fraction]


def weighted_degree(exponent: Exponent) -> int:
    if len(exponent) != len(VARIABLE_NAMES):
        raise ValueError("wrong exponent length")
    if any(not isinstance(power, int) or power < 0 for power in exponent):
        raise ValueError("exponents must be nonnegative integers")
    return sum(
        power * weight
        for power, weight in zip(exponent, VARIABLE_WEIGHTS)
    )


def mirror_exponent(exponent: Exponent) -> Exponent:
    if len(exponent) != len(VARIABLE_NAMES):
        raise ValueError("wrong exponent length")
    return tuple(exponent[index] for index in MIRROR_VARIABLE_INDEX)


def _enumerate_exponents_from(
    variable: int, remaining_degree: int, prefix: tuple[int, ...]
) -> list[Exponent]:
    if variable == len(VARIABLE_NAMES):
        return [prefix]
    weight = VARIABLE_WEIGHTS[variable]
    out = []
    maximum_power = remaining_degree // weight
    for power in range(maximum_power + 1):
        out.extend(
            _enumerate_exponents_from(
                variable + 1,
                remaining_degree - power * weight,
                prefix + (power,),
            )
        )
    return out


def raw_monomials(maximum_degree: int = 4) -> tuple[Exponent, ...]:
    if not isinstance(maximum_degree, int) or maximum_degree < 0:
        raise ValueError("maximum degree must be a nonnegative integer")
    exponents = _enumerate_exponents_from(0, maximum_degree, ())
    return tuple(sorted(exponents, key=lambda item: (weighted_degree(item), item)))


@dataclass(frozen=True)
class SymmetryBasis:
    raw: tuple[Exponent, ...]
    invariant: tuple[Polynomial, ...]
    anti_invariant: tuple[Polynomial, ...]


def symmetry_basis(maximum_degree: int = 4) -> SymmetryBasis:
    raw = raw_monomials(maximum_degree)
    raw_set = set(raw)
    seen: set[Exponent] = set()
    invariant: list[Polynomial] = []
    anti: list[Polynomial] = []
    for exponent in raw:
        if exponent in seen:
            continue
        mirrored = mirror_exponent(exponent)
        if mirrored not in raw_set:
            raise AssertionError("monomial basis is not closed under mirror")
        seen.add(exponent)
        seen.add(mirrored)
        if mirrored == exponent:
            invariant.append(((exponent, 1),))
        else:
            first, second = sorted((exponent, mirrored))
            invariant.append(((first, 1), (second, 1)))
            anti.append(((first, 1), (second, -1)))
    key = lambda polynomial: (
        weighted_degree(polynomial[0][0]),
        polynomial[0][0],
        polynomial,
    )
    return SymmetryBasis(
        raw=raw,
        invariant=tuple(sorted(invariant, key=key)),
        anti_invariant=tuple(sorted(anti, key=key)),
    )


def balanced_invariant_basis(
    maximum_degree: int = 4,
) -> tuple[Polynomial, ...]:
    """Invariant basis restricted to balanced edges, where z is identically 0."""
    return tuple(
        polynomial
        for polynomial in symmetry_basis(maximum_degree).invariant
        if any(exponent[0] == 0 for exponent, _ in polynomial)
    )


def mirror_polynomial(polynomial: Polynomial) -> Polynomial:
    terms = [
        (mirror_exponent(exponent), coefficient)
        for exponent, coefficient in polynomial
    ]
    return tuple(sorted(terms))


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


def mirror_values(values: Sequence[int]) -> tuple[int, ...]:
    if len(values) != len(VARIABLE_NAMES):
        raise ValueError("wrong feature-vector length")
    return tuple(values[index] for index in MIRROR_VARIABLE_INDEX)


def evaluate_monomial(exponent: Exponent, values: Sequence[int]) -> int:
    if len(values) != len(VARIABLE_NAMES):
        raise ValueError("wrong feature-vector length")
    result = 1
    for value, power in zip(values, exponent):
        result *= value**power
    return result


def evaluate_polynomial(polynomial: Polynomial, values: Sequence[int]) -> int:
    return sum(
        coefficient * evaluate_monomial(exponent, values)
        for exponent, coefficient in polynomial
    )


def parameter_names() -> tuple[str, ...]:
    basis = symmetry_basis()
    balanced_basis = balanced_invariant_basis()
    names = []
    for peel in PEEL_WIDTHS:
        names.extend(
            f"s{peel}:oriented:invariant:{index:02d}"
            for index in range(len(basis.invariant))
        )
        names.extend(
            f"s{peel}:oriented:anti:{index:02d}"
            for index in range(len(basis.anti_invariant))
        )
        names.extend(
            f"s{peel}:balanced:invariant:{index:02d}"
            for index in range(len(balanced_basis))
        )
    return tuple(names)


def _parameter_offsets(peel_width: int) -> tuple[int, int, int]:
    if peel_width not in PEEL_WIDTHS:
        raise ValueError("peel width must be 2 or 3")
    basis = symmetry_basis()
    balanced_basis = balanced_invariant_basis()
    per_peel = (
        len(basis.invariant)
        + len(basis.anti_invariant)
        + len(balanced_basis)
    )
    start = PEEL_WIDTHS.index(peel_width) * per_peel
    invariant = start
    anti = invariant + len(basis.invariant)
    balanced = anti + len(basis.anti_invariant)
    return invariant, anti, balanced


def normalized_flow_row(feature: EdgeFeatures) -> SparseRow:
    """Coefficient row for h(e) in the fixed 156-dimensional ansatz."""
    basis = symmetry_basis()
    balanced_basis = balanced_invariant_basis()
    values = _feature_values(feature)
    invariant_offset, anti_offset, balanced_offset = _parameter_offsets(
        feature.peel_width
    )
    row: SparseRow = {}
    if feature.peel_side == "balanced":
        for index, polynomial in enumerate(balanced_basis):
            value = evaluate_polynomial(polynomial, values)
            if value:
                row[balanced_offset + index] = Fraction(value)
        return row
    if feature.peel_side not in {"left", "right"}:
        raise ValueError(f"unknown peel side {feature.peel_side!r}")
    anti_sign = 1 if feature.peel_side == "left" else -1
    for index, polynomial in enumerate(basis.invariant):
        value = evaluate_polynomial(polynomial, values)
        if value:
            row[invariant_offset + index] = Fraction(value)
    for index, polynomial in enumerate(basis.anti_invariant):
        value = anti_sign * evaluate_polynomial(polynomial, values)
        if value:
            row[anti_offset + index] = Fraction(value)
    return row


def mirror_edge_key(feature: EdgeFeatures) -> tuple[tuple[int, ...], int, int]:
    parent = tuple(reversed(feature.parent))
    block = len(feature.parent) - 1 - feature.block_index
    left = feature.right_part
    return parent, block, left


@dataclass(frozen=True)
class DecisionSystem:
    dimensions: tuple[int, ...]
    parameter_names: tuple[str, ...]
    row_labels: tuple[tuple[int, tuple[int, ...]], ...]
    rows: tuple[Mapping[int, Fraction], ...]
    rhs: tuple[Fraction, ...]
    n_edges: int


def _add_scaled(target: SparseRow, source: Mapping[int, Fraction], scale: Fraction) -> None:
    if not scale:
        return
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        elif column in target:
            del target[column]


def build_decision_system(dimensions: Iterable[int]) -> DecisionSystem:
    dimensions = tuple(dimensions)
    if not dimensions:
        raise ValueError("dimensions must be nonempty")
    if tuple(sorted(set(dimensions))) != dimensions:
        raise ValueError("dimensions must be strictly increasing")
    if any(not isinstance(d, int) or isinstance(d, bool) or d < 2 for d in dimensions):
        raise ValueError("dimensions must be integers at least 2")
    names = parameter_names()
    labels: list[tuple[int, tuple[int, ...]]] = []
    rows: list[SparseRow] = []
    rhs: list[Fraction] = []
    n_edges = 0
    for d in dimensions:
        compositions = sorted(support_compositions(d))
        local_rows = {composition: {} for composition in compositions}
        for feature in edge_features(d):
            n_edges += 1
            edge_row = normalized_flow_row(feature)
            _add_scaled(
                local_rows[feature.parent],
                edge_row,
                feature.ratio,
            )
            _add_scaled(local_rows[feature.child], edge_row, Fraction(-1))
        for composition in compositions:
            labels.append((d, composition))
            rows.append(local_rows[composition])
            rhs.append(Fraction(s4(composition)))
    return DecisionSystem(
        dimensions=dimensions,
        parameter_names=names,
        row_labels=tuple(labels),
        rows=tuple(rows),
        rhs=tuple(rhs),
        n_edges=n_edges,
    )


def evaluate_sparse_row(
    row: Mapping[int, Fraction], coefficients: Sequence[Fraction]
) -> Fraction:
    return sum(
        (value * coefficients[column] for column, value in row.items()),
        Fraction(0),
    )


def verify_solution(
    system: DecisionSystem, coefficients: Sequence[Fraction]
) -> dict[str, Any]:
    if len(coefficients) != len(system.parameter_names):
        raise ValueError("coefficient vector has the wrong length")
    mismatches = []
    for index, (row, expected) in enumerate(zip(system.rows, system.rhs)):
        actual = evaluate_sparse_row(row, coefficients)
        if actual != expected:
            mismatches.append((index, actual, expected))
    return {
        "verified": not mismatches,
        "n_rows": len(system.rows),
        "n_parameters": len(system.parameter_names),
        "n_mismatches": len(mismatches),
        "first_mismatch": None
        if not mismatches
        else {
            "row": mismatches[0][0],
            "actual": fraction_record(mismatches[0][1]),
            "expected": fraction_record(mismatches[0][2]),
        },
    }


@dataclass
class _Pivot:
    row: SparseRow
    rhs: Fraction
    combination: SparseRow


@dataclass(frozen=True)
class EliminationResult:
    status: str
    rank: int
    solution: tuple[Fraction, ...] | None
    witness: Mapping[int, Fraction] | None
    witness_rhs: Fraction | None
    contradiction_row: int | None


def _subtract_scaled(
    target: SparseRow,
    source: Mapping[int, Fraction],
    scale: Fraction,
) -> None:
    _add_scaled(target, source, -scale)


def exact_eliminate(system: DecisionSystem) -> EliminationResult:
    """Exact sparse row echelon solve with row-provenance tracking."""
    pivots: dict[int, _Pivot] = {}
    for row_index, (source_row, source_rhs) in enumerate(
        zip(system.rows, system.rhs)
    ):
        row = dict(source_row)
        rhs = Fraction(source_rhs)
        combination: SparseRow = {row_index: Fraction(1)}
        while row:
            column = min(row)
            coefficient = row[column]
            if column in pivots:
                pivot = pivots[column]
                _subtract_scaled(row, pivot.row, coefficient)
                rhs -= coefficient * pivot.rhs
                _subtract_scaled(combination, pivot.combination, coefficient)
                continue
            reciprocal = Fraction(
                coefficient.denominator,
                coefficient.numerator,
            )
            row = {
                key: value * reciprocal for key, value in row.items()
            }
            rhs *= reciprocal
            combination = {
                key: value * reciprocal
                for key, value in combination.items()
            }
            pivots[column] = _Pivot(row, rhs, combination)
            break
        if not row and rhs:
            return EliminationResult(
                status="inconsistent",
                rank=len(pivots),
                solution=None,
                witness=combination,
                witness_rhs=rhs,
                contradiction_row=row_index,
            )

    solution = [Fraction(0) for _ in system.parameter_names]
    for column in sorted(pivots, reverse=True):
        pivot = pivots[column]
        value = pivot.rhs - sum(
            (
                coefficient * solution[later]
                for later, coefficient in pivot.row.items()
                if later != column
            ),
            Fraction(0),
        )
        solution[column] = value
    return EliminationResult(
        status="consistent",
        rank=len(pivots),
        solution=tuple(solution),
        witness=None,
        witness_rhs=None,
        contradiction_row=None,
    )


def matrix_rank(rows: Sequence[Mapping[int, Fraction]]) -> int:
    pivots: dict[int, SparseRow] = {}
    for source in rows:
        row = dict(source)
        while row:
            column = min(row)
            coefficient = row[column]
            if column in pivots:
                _subtract_scaled(row, pivots[column], coefficient)
                continue
            reciprocal = Fraction(
                coefficient.denominator,
                coefficient.numerator,
            )
            row = {key: value * reciprocal for key, value in row.items()}
            pivots[column] = row
            break
    return len(pivots)


def system_ranks(system: DecisionSystem) -> tuple[int, int]:
    coefficient_rank = matrix_rank(system.rows)
    augmented = []
    rhs_column = len(system.parameter_names)
    for row, rhs in zip(system.rows, system.rhs):
        extended = dict(row)
        if rhs:
            extended[rhs_column] = rhs
        augmented.append(extended)
    return coefficient_rank, matrix_rank(augmented)


def _lcm(first: int, second: int) -> int:
    if not first or not second:
        return 0
    return abs(first * second) // gcd(first, second)


def primitive_integer_witness(
    witness: Mapping[int, Fraction], rhs: Sequence[Fraction]
) -> tuple[dict[int, int], int]:
    if not witness:
        raise ValueError("witness must be nonempty")
    denominator_lcm = reduce(
        _lcm,
        (value.denominator for value in witness.values()),
        1,
    )
    integers = {
        index: value.numerator * (denominator_lcm // value.denominator)
        for index, value in witness.items()
        if value
    }
    divisor = reduce(gcd, (abs(value) for value in integers.values()))
    integers = {index: value // divisor for index, value in integers.items()}
    rhs_dot = sum(
        (Fraction(value) * rhs[index] for index, value in integers.items()),
        Fraction(0),
    )
    if rhs_dot.denominator != 1 or not rhs_dot:
        raise AssertionError("primitive witness has invalid RHS dot product")
    if rhs_dot < 0:
        integers = {index: -value for index, value in integers.items()}
        rhs_dot = -rhs_dot
    return integers, rhs_dot.numerator


def verify_integer_witness(
    system: DecisionSystem, witness: Mapping[int, int]
) -> dict[str, Any]:
    column_sums: SparseRow = {}
    rhs_sum = Fraction(0)
    for row_index, multiplier in witness.items():
        if not isinstance(row_index, int) or not 0 <= row_index < len(system.rows):
            raise ValueError("witness row index out of range")
        if not isinstance(multiplier, int) or isinstance(multiplier, bool):
            raise ValueError("witness multipliers must be integers")
        _add_scaled(
            column_sums,
            system.rows[row_index],
            Fraction(multiplier),
        )
        rhs_sum += multiplier * system.rhs[row_index]
    return {
        "verified": not column_sums and bool(rhs_sum),
        "n_nonzero_multipliers": sum(bool(value) for value in witness.values()),
        "n_nonzero_column_sums": len(column_sums),
        "rhs_sum": fraction_record(rhs_sum),
    }


def fraction_record(value: Fraction | int) -> dict[str, str]:
    value = Fraction(value)
    return {"num": str(value.numerator), "den": str(value.denominator)}


def polynomial_record(polynomial: Polynomial) -> list[dict[str, Any]]:
    return [
        {"exponents": list(exponent), "coefficient": coefficient}
        for exponent, coefficient in polynomial
    ]


def basis_document() -> dict[str, Any]:
    basis = symmetry_basis()
    balanced_basis = balanced_invariant_basis()
    degree_counts = {
        str(degree): sum(
            weighted_degree(exponent) == degree for exponent in basis.raw
        )
        for degree in range(5)
    }
    invariant_degree_counts = {
        str(degree): sum(
            weighted_degree(polynomial[0][0]) == degree
            for polynomial in basis.invariant
        )
        for degree in range(5)
    }
    anti_degree_counts = {
        str(degree): sum(
            weighted_degree(polynomial[0][0]) == degree
            for polynomial in basis.anti_invariant
        )
        for degree in range(5)
    }
    return {
        "schema": BASIS_SCHEMA,
        "normalization": "h(e)=f(e)/G(child)",
        "variables": [
            {
                "name": "z",
                "definition": "affected_block_size - 2*peel_width",
                "weight": 1,
            },
            {"name": "L", "definition": "sum of blocks before the split block", "weight": 1},
            {"name": "R", "definition": "sum of blocks after the split block", "weight": 1},
            {"name": "VL", "definition": "sum n(n-2) over blocks before", "weight": 2},
            {"name": "VR", "definition": "sum n(n-2) over blocks after", "weight": 2},
            {"name": "QL", "definition": "sum [n(n-2)]^2 over blocks before", "weight": 4},
            {"name": "QR", "definition": "sum [n(n-2)]^2 over blocks after", "weight": 4},
        ],
        "maximum_weighted_degree": 4,
        "mirror": {
            "composition": "reverse the parent composition",
            "split": "(p,q) maps to (q,p) in the mirrored block",
            "variables": ["z", "R", "L", "VR", "VL", "QR", "QL"],
            "peel_side": "left and right swap; balanced is fixed",
            "warning": (
                "G(reverse(c))/G(c)=first_block/last_block, so mirror "
                "equivariance is an ansatz restriction, not a symmetry "
                "deduced from the divergence equations"
            ),
        },
        "raw_monomial_count": len(basis.raw),
        "raw_degree_counts": degree_counts,
        "invariant_basis_count": len(basis.invariant),
        "invariant_degree_counts": invariant_degree_counts,
        "anti_invariant_basis_count": len(basis.anti_invariant),
        "anti_invariant_degree_counts": anti_degree_counts,
        "raw_monomials": [
            {
                "exponents": list(exponent),
                "weighted_degree": weighted_degree(exponent),
                "mirror_exponents": list(mirror_exponent(exponent)),
            }
            for exponent in basis.raw
        ],
        "invariant_basis": [
            polynomial_record(polynomial) for polynomial in basis.invariant
        ],
        "anti_invariant_basis": [
            polynomial_record(polynomial)
            for polynomial in basis.anti_invariant
        ],
        "balanced_invariant_basis_count": len(balanced_basis),
        "balanced_invariant_basis": [
            polynomial_record(polynomial) for polynomial in balanced_basis
        ],
        "edge_channels": {
            "peel_widths": list(PEEL_WIDTHS),
            "oriented": (
                "for each peel width, left/right form one equivariant pair: "
                "the invariant component is shared and the anti component "
                "changes sign"
            ),
            "balanced": (
                "for each peel width, balanced flow uses the invariant basis "
                "after removing z-divisible polynomials, which vanish "
                "identically because balanced edges have z=0"
            ),
        },
        "parameter_count": len(parameter_names()),
        "parameter_names": list(parameter_names()),
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
        "method": (
            "direct substitution into normalized exact divergence equations; "
            "no certificate coordinates read or fitted"
        ),
        "dimensions": list(system.dimensions),
        "n_rows": len(system.rows),
        "n_edges": system.n_edges,
        "n_parameters": len(system.parameter_names),
        "parameter_names": list(system.parameter_names),
        "rational_encoding": "[column, numerator_string, denominator_string]",
        "rows": rows,
    }


def solution_document(
    system: DecisionSystem, coefficients: Sequence[Fraction]
) -> dict[str, Any]:
    verification = verify_solution(system, coefficients)
    if not verification["verified"]:
        raise AssertionError("attempted to persist an invalid prefix solution")
    return {
        "schema": SOLUTION_SCHEMA,
        "dimensions": list(system.dimensions),
        "method": "exact sparse echelon solve; free parameters set to zero",
        "n_parameters": len(system.parameter_names),
        "coefficients": [fraction_record(value) for value in coefficients],
        "verification": verification,
    }


def witness_document(
    system: DecisionSystem,
    witness: Mapping[int, int],
    *,
    smallest_inconsistent_dimension: int,
) -> dict[str, Any]:
    verification = verify_integer_witness(system, witness)
    if not verification["verified"]:
        raise AssertionError("attempted to persist an invalid witness")
    rows = []
    for row_index, multiplier in sorted(witness.items()):
        if not multiplier:
            continue
        d, composition = system.row_labels[row_index]
        rows.append(
            {
                "row": row_index,
                "d": d,
                "composition": list(composition),
                "multiplier": str(multiplier),
            }
        )
    return {
        "schema": WITNESS_SCHEMA,
        "interpretation": (
            "the integer row combination has zero coefficient in every "
            "parameter column and a nonzero right-hand side"
        ),
        "dimensions": list(system.dimensions),
        "smallest_inconsistent_dimension": smallest_inconsistent_dimension,
        "n_parameters": len(system.parameter_names),
        "multipliers": rows,
        "verification": verification,
    }
