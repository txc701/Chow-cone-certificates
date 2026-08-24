"""Exact, solver-independent feature analysis for k=4 flow certificates.

The max-flow certificates in :mod:`k4_certificates` are deliberately
nonunique.  This module therefore separates three jobs:

* describe every peel-width-at-most-3 edge by exact mathematical features;
* join reproducible sparse certificates and exact coordinate ranges to those
  features without treating one solver output as canonical; and
* search fixed, dimension-shared ansatz classes by solving the normalized
  divergence equations directly over :class:`fractions.Fraction`.

No floating-point arithmetic or third-party linear algebra package is used.
In particular, ansatz coefficients are never fitted to certificate values.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb, prod
from typing import Any, Iterable, Mapping, Sequence

from k4_certificates import EdgeKey, EdgeRange, allowed_edge_keys
from k4_weights import b4_720, s4, support_w4, u_value, w4_value
from support import support_compositions


FEATURE_SCHEMA = "chow-cone/k4-edge-features/v1"
ANSATZ_SCHEMA = "chow-cone/k4-direct-ansatz/v1"
INTERVAL_WITNESS_SCHEMA = "chow-cone/k4-interval-witness/v1"

# The richer P3 class has 276 declared coefficients.  Training through d=8
# supplies only 84 node equations and cannot identify it.  The frozen split
# below supplies 372 lower-dimensional equations while retaining d=12 for a
# distinct validation phase and d=13,...,16 as genuine untouched holdouts.
DEFAULT_TRAINING_DIMENSIONS = tuple(range(3, 12))
DEFAULT_VALIDATION_DIMENSIONS = (12,)
DEFAULT_HOLDOUT_DIMENSIONS = tuple(range(13, 17))


def fraction_record(value: Fraction | int) -> dict[str, int]:
    """Return a JSON-compatible exact rational representation."""
    value = Fraction(value)
    return {"num": value.numerator, "den": value.denominator}


def _prefix_sums(composition: tuple[int, ...]) -> tuple[int, ...]:
    total = 0
    out = []
    for part in composition[:-1]:
        total += part
        out.append(total)
    return tuple(out)


def variance_statistic(block_size: int) -> int:
    """The unscaled block variance statistic ``v(n) = n(n-2)``."""
    return block_size * (block_size - 2)


def g_value(composition: tuple[int, ...], d: int) -> int:
    """Return ``G(c) = U_c * product_i (n_i - 1)`` exactly."""
    if sum(composition) != d + 2 or any(part < 2 for part in composition):
        raise ValueError("composition is not a support composition for d")
    return u_value(composition, d) * prod(part - 1 for part in composition)


def s4_simplified(composition: tuple[int, ...], d: int) -> int:
    """Compute S4 from its total-variance and square-sum statistics.

    Writing ``v_i = n_i(n_i-2)``, the expression in ``k4_weights.py`` is

        S4 = 15 (sum v_i)^2 - 6 sum v_i^2 - 12 sum v_i - B4_720(d).
    """
    if sum(composition) != d + 2:
        raise ValueError("composition has the wrong total for d")
    values = [variance_statistic(part) for part in composition]
    total = sum(values)
    square_sum = sum(value * value for value in values)
    return 15 * total * total - 6 * square_sum - 12 * total - b4_720(d)


def g_child_parent_ratio(
    block_size: int, left_part: int, is_final_block: bool
) -> Fraction:
    """Closed exact formula for ``G(child) / G(parent)``.

    A final-block split has the additional factor ``right_part/block_size``
    because the last part is singled out in the definition of ``U``.
    """
    right_part = block_size - left_part
    if left_part < 2 or right_part < 2:
        raise ValueError("both child parts must be at least 2")
    ratio = Fraction(
        comb(block_size, left_part)
        * (left_part - 1)
        * (right_part - 1),
        block_size - 1,
    )
    if is_final_block:
        ratio *= Fraction(right_part, block_size)
    return ratio


@dataclass(frozen=True)
class EdgeFeatures:
    """Exact static features of one allowed peel-width edge."""

    d: int
    parent: tuple[int, ...]
    block_index: int
    left_part: int
    child: tuple[int, ...]
    block_size: int
    right_part: int
    peel_width: int
    peel_side: str
    is_final_block: bool
    L: int
    R: int
    VL: int
    VR: int
    QL: int
    QR: int
    V: int
    Q2: int
    cross: int
    v_block: int
    v_left: int
    v_right: int
    B4_720: int
    S4_parent: int
    S4_child: int
    G_parent: int
    G_child: int
    w4_parent: int
    w4_child: int

    @property
    def edge(self) -> EdgeKey:
        return (self.parent, self.block_index, self.left_part)

    @property
    def N(self) -> int:
        return self.d + 2

    @property
    def z(self) -> int:
        """Excess of the affected block above the balanced peel baseline."""
        return self.block_size - 2 * self.peel_width

    @property
    def N_ext(self) -> int:
        return self.L + self.R

    @property
    def V_ext(self) -> int:
        return self.VL + self.VR

    @property
    def Q_ext(self) -> int:
        return self.QL + self.QR

    @property
    def ratio(self) -> Fraction:
        return Fraction(self.G_child, self.G_parent)

    @property
    def edge_type(self) -> str:
        final = "final" if self.is_final_block else "nonfinal"
        return f"s{self.peel_width}:{self.peel_side}:{final}"

    @property
    def edge_id(self) -> str:
        comp = ",".join(str(part) for part in self.parent)
        return f"d{self.d}:({comp}):i{self.block_index}:p{self.left_part}"

    def to_record(self) -> dict[str, Any]:
        """Return a JSON-compatible record with no implicit fractions."""
        parent_values = [variance_statistic(part) for part in self.parent]
        child_values = [variance_statistic(part) for part in self.child]
        return {
            "schema": FEATURE_SCHEMA,
            "edge_id": self.edge_id,
            "d": self.d,
            "N": self.N,
            "parent": list(self.parent),
            "child": list(self.child),
            "parent_block_count": len(self.parent),
            "child_block_count": len(self.child),
            "block_index": self.block_index,
            "block_position": self.block_index + 1,
            "affected_block": self.block_size,
            "left_part": self.left_part,
            "right_part": self.right_part,
            "peel_width": self.peel_width,
            "peel_side": self.peel_side,
            "is_final_block": self.is_final_block,
            "edge_type": self.edge_type,
            "z": self.z,
            "prefix_block_count": self.block_index,
            "suffix_block_count": len(self.parent) - self.block_index - 1,
            "parent_prefix_sums": list(_prefix_sums(self.parent)),
            "child_prefix_sums": list(_prefix_sums(self.child)),
            "added_subset_element": self.L + self.left_part,
            "L": self.L,
            "R": self.R,
            "N_ext": self.N_ext,
            "VL": self.VL,
            "VR": self.VR,
            "V_ext": self.V_ext,
            "QL": self.QL,
            "QR": self.QR,
            "Q_ext": self.Q_ext,
            "V": self.V,
            "Q2": self.Q2,
            "cross": self.cross,
            "v_parent_blocks": parent_values,
            "v_child_blocks": child_values,
            "v_affected": self.v_block,
            "v_left": self.v_left,
            "v_right": self.v_right,
            "delta_V": self.v_left + self.v_right - self.v_block,
            "B4_720": self.B4_720,
            "S4_parent": self.S4_parent,
            "S4_child": self.S4_child,
            "delta_S4": self.S4_child - self.S4_parent,
            "G_parent": self.G_parent,
            "G_child": self.G_child,
            "G_child_over_parent": fraction_record(self.ratio),
            "w4_parent": self.w4_parent,
            "w4_child": self.w4_child,
        }


def _make_edge_features(d: int, edge: EdgeKey) -> EdgeFeatures:
    parent, block_index, left_part = edge
    block_size = parent[block_index]
    right_part = block_size - left_part
    child = (
        parent[:block_index]
        + (left_part, right_part)
        + parent[block_index + 1 :]
    )
    left_blocks = parent[:block_index]
    right_blocks = parent[block_index + 1 :]
    left_values = [variance_statistic(part) for part in left_blocks]
    right_values = [variance_statistic(part) for part in right_blocks]
    parent_values = [variance_statistic(part) for part in parent]
    total_v = sum(parent_values)
    square_sum = sum(value * value for value in parent_values)
    cross_twice = total_v * total_v - square_sum
    if cross_twice % 2:
        raise AssertionError("pairwise cross statistic is not integral")
    if left_part == right_part:
        peel_side = "balanced"
    elif left_part < right_part:
        peel_side = "left"
    else:
        peel_side = "right"
    result = EdgeFeatures(
        d=d,
        parent=parent,
        block_index=block_index,
        left_part=left_part,
        child=child,
        block_size=block_size,
        right_part=right_part,
        peel_width=min(left_part, right_part),
        peel_side=peel_side,
        is_final_block=block_index == len(parent) - 1,
        L=sum(left_blocks),
        R=sum(right_blocks),
        VL=sum(left_values),
        VR=sum(right_values),
        QL=sum(value * value for value in left_values),
        QR=sum(value * value for value in right_values),
        V=total_v,
        Q2=square_sum,
        cross=cross_twice // 2,
        v_block=variance_statistic(block_size),
        v_left=variance_statistic(left_part),
        v_right=variance_statistic(right_part),
        B4_720=b4_720(d),
        S4_parent=s4(parent),
        S4_child=s4(child),
        G_parent=g_value(parent, d),
        G_child=g_value(child, d),
        w4_parent=w4_value(parent, d),
        w4_child=w4_value(child, d),
    )
    if result.peel_width > 3:
        raise AssertionError("feature builder received a disallowed edge")
    if result.S4_parent != s4_simplified(parent, d):
        raise AssertionError("S4 simplification failed at parent")
    if result.S4_child != s4_simplified(child, d):
        raise AssertionError("S4 simplification failed at child")
    if result.ratio != g_child_parent_ratio(
        block_size, left_part, result.is_final_block
    ):
        raise AssertionError("closed G ratio does not match exact G values")
    return result


def edge_features(d: int) -> list[EdgeFeatures]:
    """Return exact features for every allowed edge in canonical order."""
    return [_make_edge_features(d, edge) for edge in allowed_edge_keys(d)]


def edge_feature_records(d: int) -> list[dict[str, Any]]:
    """JSON-compatible form of :func:`edge_features`."""
    return [feature.to_record() for feature in edge_features(d)]


def _validate_sparse_flow(d: int, sparse_flow: Mapping[EdgeKey, int]) -> None:
    allowed = allowed_edge_keys(d)
    allowed_set = set(allowed)
    unknown = set(sparse_flow) - allowed_set
    if unknown:
        raise ValueError(f"certificate contains a disallowed edge: {min(unknown)!r}")
    divergence = {composition: 0 for composition in support_compositions(d)}
    for parent, block, left in allowed:
        value = sparse_flow.get((parent, block, left), 0)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError("certificate flows must be nonnegative integers")
        child = parent[:block] + (left, parent[block] - left) + parent[block + 1 :]
        divergence[parent] += value
        divergence[child] -= value
    weights = support_w4(d)
    for composition in sorted(weights):
        if divergence[composition] != weights[composition]:
            raise ValueError(
                "certificate divergence mismatch at "
                f"{composition}: {divergence[composition]} != {weights[composition]}"
            )
    if sum(divergence.values()) != 0:
        raise ValueError("certificate has nonzero total divergence")


def _range_component(item: EdgeRange | Mapping[str, Any], name: str) -> Any:
    if isinstance(item, Mapping):
        return item[name]
    return getattr(item, name)


def join_feature_records(
    d: int,
    certificates: Mapping[str, Mapping[EdgeKey, int]],
    edge_ranges: Mapping[EdgeKey, EdgeRange | Mapping[str, Any]] | None = None,
    *,
    validate_certificates: bool = True,
) -> list[dict[str, Any]]:
    """Join sparse certificates and optional exact ranges to every edge.

    Missing sparse coordinates are represented explicitly as zero.  The
    returned list is in canonical edge order and contains no ``Fraction`` or
    tuple objects, so it can be passed directly to ``json.dump``.
    """
    if not certificates:
        raise ValueError("at least one named certificate is required")
    for name, sparse in certificates.items():
        if not isinstance(name, str) or not name:
            raise ValueError("certificate names must be nonempty strings")
        if validate_certificates:
            _validate_sparse_flow(d, sparse)
    feature_list = edge_features(d)
    allowed = {feature.edge for feature in feature_list}
    if edge_ranges is not None:
        unknown_ranges = set(edge_ranges) - allowed
        if unknown_ranges:
            raise ValueError(
                f"ranges contain a disallowed edge: {min(unknown_ranges)!r}"
            )

    records = []
    for feature in feature_list:
        record = feature.to_record()
        flow_records: dict[str, Any] = {}
        for name in sorted(certificates):
            value = certificates[name].get(feature.edge, 0)
            flow_records[name] = {
                "flow": value,
                "used": value > 0,
                "normalized_flow": fraction_record(
                    Fraction(value, feature.G_child)
                ),
            }
        record["certificates"] = flow_records
        if edge_ranges is not None and feature.edge in edge_ranges:
            item = edge_ranges[feature.edge]
            minimum = int(_range_component(item, "minimum"))
            current = int(_range_component(item, "current"))
            maximum = int(_range_component(item, "maximum"))
            if not 0 <= minimum <= current <= maximum:
                raise ValueError(f"invalid edge range at {feature.edge!r}")
            record["edge_range"] = {
                "minimum": minimum,
                "current": current,
                "maximum": maximum,
                "classification": str(_range_component(item, "classification")),
                "normalized_minimum": fraction_record(
                    Fraction(minimum, feature.G_child)
                ),
                "normalized_current": fraction_record(
                    Fraction(current, feature.G_child)
                ),
                "normalized_maximum": fraction_record(
                    Fraction(maximum, feature.G_child)
                ),
            }
        records.append(record)
    return records


@dataclass(frozen=True)
class ExactLinearSolution:
    """Deterministic RREF result for an exact rational linear system."""

    status: str
    rank: int
    n_variables: int
    pivot_columns: tuple[int, ...]
    free_columns: tuple[int, ...]
    solution: tuple[Fraction, ...] | None
    inconsistent_row: int | None


def solve_fraction_system(
    matrix: Sequence[Sequence[Fraction | int]],
    rhs: Sequence[Fraction | int],
    *,
    n_variables: int | None = None,
) -> ExactLinearSolution:
    """Solve ``matrix * x = rhs`` by deterministic exact Gauss-Jordan RREF.

    For a consistent underdetermined system, ``solution`` is the canonical
    particular solution obtained by setting every free variable to zero.  Its
    status remains ``"underdetermined"``; callers must not mistake that
    arbitrary representative for an identified structural rule.
    """
    if len(matrix) != len(rhs):
        raise ValueError("matrix row count and rhs length differ")
    if matrix:
        width = len(matrix[0])
        if any(len(row) != width for row in matrix):
            raise ValueError("matrix is ragged")
        if n_variables is not None and n_variables != width:
            raise ValueError("n_variables disagrees with matrix width")
        n_variables = width
    elif n_variables is None:
        n_variables = 0
    if n_variables < 0:
        raise ValueError("n_variables must be nonnegative")

    rows = [
        [Fraction(value) for value in row] + [Fraction(target)]
        for row, target in zip(matrix, rhs)
    ]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(n_variables):
        selected = next(
            (row for row in range(pivot_row, len(rows)) if rows[row][column]),
            None,
        )
        if selected is None:
            continue
        rows[pivot_row], rows[selected] = rows[selected], rows[pivot_row]
        pivot = rows[pivot_row][column]
        reciprocal = Fraction(pivot.denominator, pivot.numerator)
        rows[pivot_row] = [entry * reciprocal for entry in rows[pivot_row]]
        for row in range(len(rows)):
            if row == pivot_row or not rows[row][column]:
                continue
            multiplier = rows[row][column]
            rows[row] = [
                entry - multiplier * pivot_entry
                for entry, pivot_entry in zip(rows[row], rows[pivot_row])
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(rows):
            break

    for row_index, row in enumerate(rows):
        if not any(row[:n_variables]) and row[n_variables]:
            return ExactLinearSolution(
                status="inconsistent",
                rank=len(pivot_columns),
                n_variables=n_variables,
                pivot_columns=tuple(pivot_columns),
                free_columns=tuple(
                    column
                    for column in range(n_variables)
                    if column not in pivot_columns
                ),
                solution=None,
                inconsistent_row=row_index,
            )

    free_columns = tuple(
        column for column in range(n_variables) if column not in pivot_columns
    )
    solution = [Fraction(0) for _ in range(n_variables)]
    for row_index, column in enumerate(pivot_columns):
        solution[column] = rows[row_index][n_variables]
    status = "unique" if not free_columns else "underdetermined"
    return ExactLinearSolution(
        status=status,
        rank=len(pivot_columns),
        n_variables=n_variables,
        pivot_columns=tuple(pivot_columns),
        free_columns=free_columns,
        solution=tuple(solution),
        inconsistent_row=None,
    )


BASIS_COLUMNS: dict[str, tuple[str, ...]] = {
    "P0": ("one",),
    "P1": ("one", "z", "z2"),
    "P2": (
        "one",
        "z",
        "z2",
        "z3",
        "z4",
        "N_ext",
        "N_ext2",
        "z_N_ext",
        "V_ext",
        "z_V_ext",
        "z2_V_ext",
        "V_ext2",
        "Q_ext",
    ),
    "P3": (
        "one",
        "z",
        "z2",
        "z3",
        "z4",
        "L",
        "R",
        "L2",
        "L_R",
        "R2",
        "z_L",
        "z_R",
        "VL",
        "VR",
        "z_VL",
        "z_VR",
        "z2_VL",
        "z2_VR",
        "QL",
        "QR",
        "VL2",
        "VL_VR",
        "VR2",
    ),
}


def ansatz_basis_values(feature: EdgeFeatures, basis: str) -> tuple[int, ...]:
    """Evaluate one of the fixed P0--P3 bases on an edge."""
    if basis not in BASIS_COLUMNS:
        raise ValueError(f"unknown ansatz basis {basis!r}")
    z = feature.z
    n_ext = feature.L + feature.R
    v_ext = feature.VL + feature.VR
    q_ext = feature.QL + feature.QR
    values = {
        "one": 1,
        "z": z,
        "z2": z * z,
        "z3": z**3,
        "z4": z**4,
        "N_ext": n_ext,
        "N_ext2": n_ext * n_ext,
        "z_N_ext": z * n_ext,
        "V_ext": v_ext,
        "z_V_ext": z * v_ext,
        "z2_V_ext": z * z * v_ext,
        "V_ext2": v_ext * v_ext,
        "Q_ext": q_ext,
        "L": feature.L,
        "R": feature.R,
        "L2": feature.L * feature.L,
        "L_R": feature.L * feature.R,
        "R2": feature.R * feature.R,
        "z_L": z * feature.L,
        "z_R": z * feature.R,
        "VL": feature.VL,
        "VR": feature.VR,
        "z_VL": z * feature.VL,
        "z_VR": z * feature.VR,
        "z2_VL": z * z * feature.VL,
        "z2_VR": z * z * feature.VR,
        "QL": feature.QL,
        "QR": feature.QR,
        "VL2": feature.VL * feature.VL,
        "VL_VR": feature.VL * feature.VR,
        "VR2": feature.VR * feature.VR,
    }
    return tuple(values[name] for name in BASIS_COLUMNS[basis])


@dataclass(frozen=True)
class AnsatzSystem:
    basis: str
    dimensions: tuple[int, ...]
    parameter_names: tuple[tuple[str, str], ...]
    row_labels: tuple[tuple[int, tuple[int, ...]], ...]
    matrix: tuple[tuple[Fraction, ...], ...]
    rhs: tuple[Fraction, ...]


def build_ansatz_system(
    dimensions: Iterable[int], basis: str
) -> AnsatzSystem:
    """Build the normalized divergence system without reading certificates."""
    if basis not in BASIS_COLUMNS:
        raise ValueError(f"unknown ansatz basis {basis!r}")
    dimensions = tuple(sorted(set(dimensions)))
    if not dimensions or any(d < 2 for d in dimensions):
        raise ValueError("ansatz dimensions must be nonempty and at least 2")
    by_dimension = {d: edge_features(d) for d in dimensions}
    edge_types = sorted(
        {feature.edge_type for features in by_dimension.values() for feature in features}
    )
    parameter_names = tuple(
        (edge_type, column)
        for edge_type in edge_types
        for column in BASIS_COLUMNS[basis]
    )
    parameter_index = {name: i for i, name in enumerate(parameter_names)}
    row_labels: list[tuple[int, tuple[int, ...]]] = []
    matrix: list[tuple[Fraction, ...]] = []
    rhs: list[Fraction] = []

    for d in dimensions:
        compositions = sorted(support_compositions(d))
        row_index = {composition: i for i, composition in enumerate(compositions)}
        rows = [
            [Fraction(0) for _ in parameter_names] for _ in compositions
        ]
        for feature in by_dimension[d]:
            values = ansatz_basis_values(feature, basis)
            parent_row = rows[row_index[feature.parent]]
            child_row = rows[row_index[feature.child]]
            for column, value in zip(BASIS_COLUMNS[basis], values):
                index = parameter_index[(feature.edge_type, column)]
                parent_row[index] += feature.ratio * value
                child_row[index] -= value
        for composition, row in zip(compositions, rows):
            row_labels.append((d, composition))
            matrix.append(tuple(row))
            rhs.append(Fraction(s4(composition)))
    return AnsatzSystem(
        basis=basis,
        dimensions=dimensions,
        parameter_names=parameter_names,
        row_labels=tuple(row_labels),
        matrix=tuple(matrix),
        rhs=tuple(rhs),
    )


def _solution_mapping(
    system: AnsatzSystem, solution: Sequence[Fraction]
) -> dict[tuple[str, str], Fraction]:
    return {
        name: Fraction(value)
        for name, value in zip(system.parameter_names, solution)
    }


def _phase_check(
    dimensions: Sequence[int],
    basis: str,
    coefficients: Mapping[tuple[str, str], Fraction],
) -> dict[str, Any]:
    dimensions = tuple(dimensions)
    negative = []
    missing_types = set()
    mismatches = []
    n_edges = 0
    n_nodes = 0
    for d in dimensions:
        compositions = sorted(support_compositions(d))
        n_nodes += len(compositions)
        divergence = {composition: Fraction(0) for composition in compositions}
        for feature in edge_features(d):
            n_edges += 1
            values = ansatz_basis_values(feature, basis)
            keys = [
                (feature.edge_type, column) for column in BASIS_COLUMNS[basis]
            ]
            if any(key not in coefficients for key in keys):
                missing_types.add(feature.edge_type)
                continue
            h_value = sum(
                coefficients[key] * value for key, value in zip(keys, values)
            )
            if h_value < 0:
                negative.append((feature, h_value))
            divergence[feature.parent] += feature.ratio * h_value
            divergence[feature.child] -= h_value
        if not missing_types:
            for composition in compositions:
                expected = Fraction(s4(composition))
                if divergence[composition] != expected:
                    mismatches.append(
                        (d, composition, divergence[composition], expected)
                    )
    first_negative = None
    if negative:
        feature, value = negative[0]
        first_negative = {
            "edge_id": feature.edge_id,
            "normalized_flow": fraction_record(value),
        }
    first_mismatch = None
    if mismatches:
        d, composition, actual, expected = mismatches[0]
        first_mismatch = {
            "d": d,
            "composition": list(composition),
            "actual": fraction_record(actual),
            "expected": fraction_record(expected),
        }
    return {
        "dimensions": list(dimensions),
        "n_nodes": n_nodes,
        "n_edges": n_edges,
        "missing_edge_types": sorted(missing_types),
        "all_nonnegative": not negative and not missing_types,
        "negative_edge_count": len(negative),
        "first_negative_edge": first_negative,
        "exact_divergence": not mismatches and not missing_types,
        "divergence_mismatch_count": len(mismatches),
        "first_divergence_mismatch": first_mismatch,
    }


def _validate_dimension_split(
    training_dimensions: Sequence[int],
    validation_dimensions: Sequence[int],
    holdout_dimensions: Sequence[int],
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    phases = {
        "training": tuple(training_dimensions),
        "validation": tuple(validation_dimensions),
        "holdout": tuple(holdout_dimensions),
    }
    for name, dimensions in phases.items():
        if not dimensions:
            raise ValueError(f"{name} dimensions must be nonempty")
        if len(set(dimensions)) != len(dimensions):
            raise ValueError(f"{name} dimensions contain duplicates")
        if any(
            not isinstance(d, int) or isinstance(d, bool) or d < 2
            for d in dimensions
        ):
            raise ValueError(f"{name} dimensions must be integers at least 2")
        phases[name] = tuple(sorted(dimensions))
    training = phases["training"]
    validation = phases["validation"]
    holdout = phases["holdout"]
    if not max(training) < min(validation) <= max(validation) < min(holdout):
        raise ValueError(
            "dimension split must be disjoint and strictly ordered: "
            "training < validation < holdout"
        )
    return training, validation, holdout


def search_ansatz_class(
    basis: str,
    *,
    training_dimensions: Sequence[int] = DEFAULT_TRAINING_DIMENSIONS,
    validation_dimensions: Sequence[int] = DEFAULT_VALIDATION_DIMENSIONS,
    holdout_dimensions: Sequence[int] = DEFAULT_HOLDOUT_DIMENSIONS,
) -> dict[str, Any]:
    """Search one fixed ansatz class by exact direct-divergence equations.

    An inconsistent or underdetermined training system is reported as such and
    does not pass.  Only a unique exact solution proceeds to nonnegativity,
    validation, and untouched holdout checks.
    """
    training_dimensions, validation_dimensions, holdout_dimensions = (
        _validate_dimension_split(
            training_dimensions,
            validation_dimensions,
            holdout_dimensions,
        )
    )
    system = build_ansatz_system(training_dimensions, basis)
    solved = solve_fraction_system(
        system.matrix, system.rhs, n_variables=len(system.parameter_names)
    )
    fit = {
        "status": solved.status,
        "n_equations": len(system.matrix),
        "n_parameters": solved.n_variables,
        "rank": solved.rank,
        "n_free_parameters": len(solved.free_columns),
        "free_parameters": [
            {
                "edge_type": system.parameter_names[index][0],
                "basis_column": system.parameter_names[index][1],
            }
            for index in solved.free_columns
        ],
        "inconsistent_row": solved.inconsistent_row,
    }
    result: dict[str, Any] = {
        "schema": ANSATZ_SCHEMA,
        "basis": basis,
        "basis_columns": list(BASIS_COLUMNS[basis]),
        "training_dimensions": list(system.dimensions),
        "validation_dimensions": list(validation_dimensions),
        "holdout_dimensions": list(holdout_dimensions),
        "solver": "deterministic Fraction Gauss-Jordan RREF",
        "fit": fit,
        "coefficients": None,
        "phase_checks": {},
        "status": solved.status,
        "passed": False,
    }
    if solved.status != "unique" or solved.solution is None:
        return result

    coefficients = _solution_mapping(system, solved.solution)
    result["coefficients"] = [
        {
            "edge_type": edge_type,
            "basis_column": column,
            "value": fraction_record(coefficients[(edge_type, column)]),
        }
        for edge_type, column in system.parameter_names
    ]
    training_check = _phase_check(
        system.dimensions, basis, coefficients
    )
    result["phase_checks"]["training"] = training_check
    if not training_check["all_nonnegative"]:
        result["status"] = "nonnegative_failure"
        return result
    if not training_check["exact_divergence"]:
        result["status"] = "training_divergence_failure"
        return result

    validation_check = _phase_check(validation_dimensions, basis, coefficients)
    result["phase_checks"]["validation"] = validation_check
    if not (
        validation_check["all_nonnegative"]
        and validation_check["exact_divergence"]
    ):
        result["status"] = "validation_failure"
        return result

    holdout_check = _phase_check(holdout_dimensions, basis, coefficients)
    result["phase_checks"]["holdout"] = holdout_check
    if not (
        holdout_check["all_nonnegative"] and holdout_check["exact_divergence"]
    ):
        result["status"] = "holdout_failure"
        return result
    result["status"] = "passed"
    result["passed"] = True
    return result


def search_ansatz_classes(
    bases: Sequence[str] = ("P0", "P1", "P2", "P3"),
    *,
    training_dimensions: Sequence[int] = DEFAULT_TRAINING_DIMENSIONS,
    validation_dimensions: Sequence[int] = DEFAULT_VALIDATION_DIMENSIONS,
    holdout_dimensions: Sequence[int] = DEFAULT_HOLDOUT_DIMENSIONS,
) -> dict[str, Any]:
    """Run the predeclared P0--P3 hierarchy with a frozen data split."""
    return {
        "schema": ANSATZ_SCHEMA,
        "method": "direct normalized divergence; no certificate values used",
        "training_dimensions": list(training_dimensions),
        "validation_dimensions": list(validation_dimensions),
        "holdout_dimensions": list(holdout_dimensions),
        "results": [
            search_ansatz_class(
                basis,
                training_dimensions=training_dimensions,
                validation_dimensions=validation_dimensions,
                holdout_dimensions=holdout_dimensions,
            )
            for basis in bases
        ],
    }


def ansatz_training_prefix_diagnostics(
    bases: Sequence[str] = ("P0", "P1", "P2", "P3"),
    *,
    first_dimension: int = 3,
    last_dimension: int = 11,
) -> list[dict[str, Any]]:
    """Locate the first inconsistent lower-dimensional training prefix.

    Once a prefix is inconsistent, every larger prefix is also inconsistent,
    so the diagnostic stops at that exact obstruction threshold.
    """
    if first_dimension < 2 or last_dimension < first_dimension:
        raise ValueError("invalid ansatz training-prefix bounds")
    results = []
    for basis in bases:
        steps = []
        first_inconsistent = None
        for top_dimension in range(first_dimension, last_dimension + 1):
            system = build_ansatz_system(
                range(first_dimension, top_dimension + 1), basis
            )
            solved = solve_fraction_system(
                system.matrix,
                system.rhs,
                n_variables=len(system.parameter_names),
            )
            steps.append(
                {
                    "maximum_training_dimension": top_dimension,
                    "status": solved.status,
                    "rank": solved.rank,
                    "n_parameters": solved.n_variables,
                    "n_equations": len(system.matrix),
                    "n_free_parameters": len(solved.free_columns),
                }
            )
            if solved.status == "inconsistent":
                first_inconsistent = top_dimension
                break
        results.append(
            {
                "basis": basis,
                "first_training_dimension": first_dimension,
                "last_dimension_examined": steps[-1][
                    "maximum_training_dimension"
                ],
                "first_inconsistent_maximum_dimension": first_inconsistent,
                "steps": steps,
            }
        )
    return results


SIGNATURE_LEVELS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "block_local",
        ("peel_width", "peel_side", "is_final_block", "block_size"),
    ),
    (
        "prefix_state",
        (
            "peel_width",
            "peel_side",
            "is_final_block",
            "block_size",
            "L",
            "VL",
        ),
    ),
    (
        "symmetric_moment_state",
        (
            "peel_width",
            "peel_side",
            "is_final_block",
            "block_size",
            "N_ext",
            "V_ext",
            "Q_ext",
        ),
    ),
    (
        "two_sided_state",
        (
            "peel_width",
            "peel_side",
            "is_final_block",
            "block_size",
            "L",
            "R",
            "VL",
            "VR",
        ),
    ),
    (
        "moment_state",
        (
            "peel_width",
            "peel_side",
            "is_final_block",
            "block_size",
            "L",
            "R",
            "VL",
            "VR",
            "QL",
            "QR",
        ),
    ),
)


def _signature_value(feature: EdgeFeatures, field: str) -> Any:
    return getattr(feature, field)


def _normalized_range(
    feature: EdgeFeatures, item: EdgeRange | Mapping[str, Any]
) -> tuple[Fraction, Fraction]:
    minimum = int(_range_component(item, "minimum"))
    maximum = int(_range_component(item, "maximum"))
    if minimum < 0 or maximum < minimum:
        raise ValueError(f"invalid coordinate range at {feature.edge!r}")
    return Fraction(minimum, feature.G_child), Fraction(maximum, feature.G_child)


def smallest_disjoint_interval_witnesses(
    ranges_by_dimension: Mapping[
        int, Mapping[EdgeKey, EdgeRange | Mapping[str, Any]]
    ],
    *,
    max_d: int = 10,
) -> dict[str, Any]:
    """Find the smallest solver-independent pair at each signature level.

    Two edges with the same declared local signature cannot share a single
    normalized rule if their exact feasible coordinate intervals are
    disjoint.  Selection is deterministic: minimize maximum dimension, then
    dimension sum, dimensions, and canonical edge keys.
    """
    occurrences: list[
        tuple[int, EdgeFeatures, EdgeRange | Mapping[str, Any]]
    ] = []
    for d in sorted(ranges_by_dimension):
        if d > max_d:
            continue
        feature_map = {feature.edge: feature for feature in edge_features(d)}
        for edge in sorted(ranges_by_dimension[d]):
            if edge not in feature_map:
                raise ValueError(f"range contains a disallowed d={d} edge: {edge!r}")
            occurrences.append((d, feature_map[edge], ranges_by_dimension[d][edge]))

    level_results = []
    for level_name, fields in SIGNATURE_LEVELS:
        groups: dict[tuple[Any, ...], list[Any]] = {}
        for occurrence in occurrences:
            _, feature, _ = occurrence
            signature = tuple(_signature_value(feature, field) for field in fields)
            groups.setdefault(signature, []).append(occurrence)
        candidates = []
        pairs_checked = 0
        for signature in sorted(groups, key=repr):
            group = sorted(
                groups[signature],
                key=lambda item: (item[0], item[1].edge),
            )
            for first, second in combinations(group, 2):
                pairs_checked += 1
                d1, feature1, range1 = first
                d2, feature2, range2 = second
                low1, high1 = _normalized_range(feature1, range1)
                low2, high2 = _normalized_range(feature2, range2)
                if high1 < low2:
                    gap = low2 - high1
                elif high2 < low1:
                    gap = low1 - high2
                else:
                    continue
                key = (
                    max(d1, d2),
                    d1 + d2,
                    d1,
                    d2,
                    feature1.edge,
                    feature2.edge,
                )
                candidates.append(
                    (
                        key,
                        signature,
                        feature1,
                        (low1, high1),
                        feature2,
                        (low2, high2),
                        gap,
                    )
                )
        witness = None
        if candidates:
            (
                _,
                signature,
                feature1,
                interval1,
                feature2,
                interval2,
                gap,
            ) = min(candidates, key=lambda item: item[0])
            witness = {
                "signature": {
                    field: value for field, value in zip(fields, signature)
                },
                "first_edge": feature1.to_record(),
                "first_normalized_interval": {
                    "minimum": fraction_record(interval1[0]),
                    "maximum": fraction_record(interval1[1]),
                },
                "second_edge": feature2.to_record(),
                "second_normalized_interval": {
                    "minimum": fraction_record(interval2[0]),
                    "maximum": fraction_record(interval2[1]),
                },
                "gap": fraction_record(gap),
                "interpretation": (
                    "all feasible certificates force disjoint normalized "
                    "ranges on two edges with the same declared signature"
                ),
            }
        level_results.append(
            {
                "level": level_name,
                "signature_fields": list(fields),
                "n_repeated_signature_groups": sum(
                    len(group) > 1 for group in groups.values()
                ),
                "pairs_checked": pairs_checked,
                "witness": witness,
            }
        )
    return {
        "schema": INTERVAL_WITNESS_SCHEMA,
        "dimensions_analyzed": [
            d for d in sorted(ranges_by_dimension) if d <= max_d
        ],
        "max_d": max_d,
        "method": "exact normalized coordinate intervals; no solver tie-breaking",
        "levels": level_results,
    }
