"""Exact cumulative equality scan for the 276-column desymmetrized ansatz.

The scan uses one shared coefficient vector for every dimension.  It starts
at d=4, adjoins one complete dimension block at a time, and stops at the
first exact equality inconsistency or after d=10.  It never imposes edgewise
nonnegativity and never adds endpoint features.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import comb, gcd
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from k4_degree4_decision import (
    DecisionSystem,
    evaluate_sparse_row,
    exact_eliminate,
    fraction_record,
    matrix_rank,
    primitive_integer_witness,
    system_ranks,
    verify_solution,
)
from k4_desymmetrized_d4 import (
    lifted_normalized_flow_row,
    lifted_parameter_names,
)
from k4_feature_analysis import edge_features, g_value
from k4_weights import s4
from support import support_compositions


CHECKPOINT_BASE = "199b5d4462858d9e8337afce001fbd23724699c9"
MINIMUM_DIMENSION = 4
MAXIMUM_DIMENSION = 10
SCAN_SCHEMA = "chow-cone/k4-desymmetrized-progressive-equality/v1"
SparseRow = dict[int, Fraction]


@dataclass(frozen=True)
class DeduplicatedSystem:
    system: DecisionSystem
    retained_raw_rows: tuple[int, ...]
    raw_to_deduplicated: tuple[int, ...]


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
    """Build one exact dimension block in canonical composition order."""
    if not isinstance(d, int) or isinstance(d, bool):
        raise ValueError("dimension must be an integer")
    if not MINIMUM_DIMENSION <= d <= MAXIMUM_DIMENSION:
        raise ValueError("this bounded scan only permits dimensions 4 through 10")
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


def _validate_dimension_prefix(maximum_dimension: int) -> tuple[int, ...]:
    if not isinstance(maximum_dimension, int) or isinstance(
        maximum_dimension, bool
    ):
        raise ValueError("maximum dimension must be an integer")
    if not MINIMUM_DIMENSION <= maximum_dimension <= MAXIMUM_DIMENSION:
        raise ValueError("maximum dimension must lie between 4 and 10")
    return tuple(range(MINIMUM_DIMENSION, maximum_dimension + 1))


def stack_systems(systems: Sequence[DecisionSystem]) -> DecisionSystem:
    """Stack dimension blocks while retaining one shared parameter vector."""
    if not systems:
        raise ValueError("at least one dimension block is required")
    names = systems[0].parameter_names
    dimensions: list[int] = []
    labels: list[tuple[int, tuple[int, ...]]] = []
    rows: list[Mapping[int, Fraction]] = []
    rhs: list[Fraction] = []
    n_edges = 0
    for system in systems:
        if system.parameter_names != names:
            raise ValueError("dimension blocks do not share one coefficient vector")
        if len(system.dimensions) != 1:
            raise ValueError("stack_systems expects single-dimension blocks")
        dimensions.extend(system.dimensions)
        labels.extend(system.row_labels)
        rows.extend(system.rows)
        rhs.extend(system.rhs)
        n_edges += system.n_edges
    if tuple(sorted(set(dimensions))) != tuple(dimensions):
        raise ValueError("dimension blocks must be strictly increasing")
    return DecisionSystem(
        dimensions=tuple(dimensions),
        parameter_names=names,
        row_labels=tuple(labels),
        rows=tuple(rows),
        rhs=tuple(rhs),
        n_edges=n_edges,
    )


def build_cumulative_system(maximum_dimension: int) -> DecisionSystem:
    dimensions = _validate_dimension_prefix(maximum_dimension)
    return stack_systems(tuple(build_dimension_system(d) for d in dimensions))


def _lcm(first: int, second: int) -> int:
    if not first or not second:
        return 0
    return abs(first * second) // gcd(first, second)


def canonical_equation_key(
    row: Mapping[int, Fraction],
    rhs: Fraction,
) -> tuple[tuple[tuple[int, int], ...], int]:
    """Canonicalize an equation up to multiplication by a nonzero scalar."""
    values = tuple(Fraction(value) for value in row.values()) + (Fraction(rhs),)
    nonzero = tuple(value for value in values if value)
    if not nonzero:
        return (), 0
    denominator = reduce(_lcm, (value.denominator for value in nonzero), 1)
    integer_row = {
        column: value.numerator * (denominator // value.denominator)
        for column, raw_value in row.items()
        if (value := Fraction(raw_value))
    }
    rhs_value = Fraction(rhs)
    integer_rhs = rhs_value.numerator * (denominator // rhs_value.denominator)
    divisor = reduce(
        gcd,
        (
            abs(value)
            for value in tuple(integer_row.values()) + (integer_rhs,)
            if value
        ),
    )
    integer_row = {
        column: value // divisor for column, value in integer_row.items()
    }
    integer_rhs //= divisor
    augmented_entries = tuple(sorted(integer_row.items()))
    first_value = augmented_entries[0][1] if augmented_entries else integer_rhs
    if first_value < 0:
        augmented_entries = tuple(
            (column, -value) for column, value in augmented_entries
        )
        integer_rhs = -integer_rhs
    return augmented_entries, integer_rhs


def deduplicate_system(system: DecisionSystem) -> DeduplicatedSystem:
    """Drop only equations proportional as complete augmented rows."""
    by_key: dict[tuple[tuple[tuple[int, int], ...], int], int] = {}
    retained: list[int] = []
    raw_to_deduplicated: list[int] = []
    for raw_index, (row, rhs) in enumerate(zip(system.rows, system.rhs)):
        key = canonical_equation_key(row, rhs)
        if key not in by_key:
            by_key[key] = len(retained)
            retained.append(raw_index)
        raw_to_deduplicated.append(by_key[key])
    reduced = DecisionSystem(
        dimensions=system.dimensions,
        parameter_names=system.parameter_names,
        row_labels=tuple(system.row_labels[index] for index in retained),
        rows=tuple(system.rows[index] for index in retained),
        rhs=tuple(system.rhs[index] for index in retained),
        n_edges=system.n_edges,
    )
    return DeduplicatedSystem(
        system=reduced,
        retained_raw_rows=tuple(retained),
        raw_to_deduplicated=tuple(raw_to_deduplicated),
    )


def _fraction_pair(value: Fraction) -> tuple[str, str]:
    value = Fraction(value)
    return str(value.numerator), str(value.denominator)


def _matrix_payload(system: DecisionSystem) -> dict[str, Any]:
    return {
        "n_rows": len(system.rows),
        "n_columns": len(system.parameter_names),
        "rows": [
            [
                [column, *_fraction_pair(value)]
                for column, value in sorted(row.items())
            ]
            for row in system.rows
        ],
    }


def _rhs_payload(system: DecisionSystem) -> dict[str, Any]:
    return {"n_rows": len(system.rhs), "rhs": [_fraction_pair(x) for x in system.rhs]}


def _system_payload(system: DecisionSystem) -> dict[str, Any]:
    return {
        "schema": SCAN_SCHEMA,
        "dimensions": list(system.dimensions),
        "parameter_names": list(system.parameter_names),
        "row_labels": [
            [d, list(composition)] for d, composition in system.row_labels
        ],
        "matrix": _matrix_payload(system),
        "rhs": _rhs_payload(system),
    }


def _json_sha256(document: Any) -> str:
    encoded = json.dumps(
        document,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def system_hashes(system: DecisionSystem) -> dict[str, str]:
    return {
        "matrix_sha256": _json_sha256(_matrix_payload(system)),
        "rhs_sha256": _json_sha256(_rhs_payload(system)),
        "system_sha256": _json_sha256(_system_payload(system)),
    }


def _left_dot_columns(
    system: DecisionSystem,
    multipliers: Mapping[int, int] | Sequence[int],
) -> tuple[SparseRow, Fraction]:
    if isinstance(multipliers, Mapping):
        indexed = multipliers.items()
    else:
        if len(multipliers) != len(system.rows):
            raise ValueError("left multiplier has the wrong length")
        indexed = enumerate(multipliers)
    columns: SparseRow = {}
    rhs = Fraction(0)
    for row_index, multiplier in indexed:
        if not multiplier:
            continue
        _add_scaled(columns, system.rows[row_index], Fraction(multiplier))
        rhs += multiplier * system.rhs[row_index]
    return columns, rhs


def d4_conservation_relation() -> dict[str, Any]:
    """Return and verify the unique primitive d=4 left-null relation."""
    system = build_dimension_system(4)
    g_values = tuple(
        g_value(composition, 4) for _, composition in system.row_labels
    )
    divisor = reduce(gcd, g_values)
    vector = tuple(value // divisor for value in g_values)
    columns, target = _left_dot_columns(system, vector)
    rank = matrix_rank(system.rows)
    if rank != len(system.rows) - 1:
        raise AssertionError("d=4 coefficient matrix does not have left nullity one")
    if columns or target:
        raise AssertionError("d=4 conservation relation failed exact verification")
    return {
        "row_order": [
            {"d": d, "composition": list(composition)}
            for d, composition in system.row_labels
        ],
        "primitive_integer_vector": [str(value) for value in vector],
        "G_values": [str(value) for value in g_values],
        "G_common_divisor": str(divisor),
        "rhs": [fraction_record(value) for value in system.rhs],
        "coefficient_rank": rank,
        "left_nullity": len(system.rows) - rank,
        "verification": {
            "nonzero_column_sums": len(columns),
            "target_dot": fraction_record(target),
        },
        "interpretation": (
            "global normalized-divergence conservation: weighting row c by "
            "G(c) cancels every edge as +G(child)-G(child); rank four makes "
            "this structural relation the full d=4 left kernel"
        ),
    }


def _subsystem(system: DecisionSystem, indices: Iterable[int]) -> DecisionSystem:
    selected = tuple(indices)
    return DecisionSystem(
        dimensions=tuple(sorted({system.row_labels[index][0] for index in selected})),
        parameter_names=system.parameter_names,
        row_labels=tuple(system.row_labels[index] for index in selected),
        rows=tuple(system.rows[index] for index in selected),
        rhs=tuple(system.rhs[index] for index in selected),
        n_edges=system.n_edges,
    )


def _is_inconsistent(system: DecisionSystem) -> bool:
    coefficient_rank, augmented_rank = system_ranks(system)
    return augmented_rank > coefficient_rank


def _extract_primitive_witness(system: DecisionSystem) -> dict[int, int]:
    elimination = exact_eliminate(system)
    if elimination.status != "inconsistent" or elimination.witness is None:
        raise ValueError("system is not inconsistent")
    witness, _ = primitive_integer_witness(elimination.witness, system.rhs)
    return witness


def inclusion_minimize_witness(
    system: DecisionSystem,
    witness: Mapping[int, int],
) -> tuple[dict[int, int], dict[str, Any]]:
    """Reverse-delete to an exact inclusion-minimal inconsistent subsystem."""
    support = sorted(index for index, value in witness.items() if value)
    initial_size = len(support)
    for candidate in tuple(reversed(support)):
        trial = tuple(index for index in support if index != candidate)
        if trial and _is_inconsistent(_subsystem(system, trial)):
            support = list(trial)
    minimized_system = _subsystem(system, support)
    local_witness = _extract_primitive_witness(minimized_system)
    global_witness = {
        support[local_index]: multiplier
        for local_index, multiplier in local_witness.items()
        if multiplier
    }
    deletion_checks = []
    for row_index in support:
        trial = tuple(index for index in support if index != row_index)
        consistent = not trial or not _is_inconsistent(_subsystem(system, trial))
        deletion_checks.append({"row": row_index, "consistent_after_deletion": consistent})
        if not consistent:
            raise AssertionError("witness support is not inclusion-minimal")
    return global_witness, {
        "method": "exact reverse deletion; no floating-point optimization",
        "initial_support_size": initial_size,
        "final_support_size": len(support),
        "notion": "inclusion-minimal",
        "deletion_checks": deletion_checks,
    }


def _count_subsets_below(n_rows: int, support_size: int, limit: int) -> int | None:
    total = 0
    for size in range(1, support_size):
        total += comb(n_rows, size)
        if total > limit:
            return None
    return total


def certify_minimum_cardinality_if_feasible(
    system: DecisionSystem,
    witness: Mapping[int, int],
    *,
    enumeration_limit: int = 200000,
) -> dict[str, Any]:
    """Exhaustively rule out smaller supports when the exact search is bounded."""
    support_size = sum(bool(value) for value in witness.values())
    subset_count = _count_subsets_below(
        len(system.rows), support_size, enumeration_limit
    )
    if subset_count is None:
        return {
            "certified": False,
            "reason": (
                "exhaustive exact search would exceed the fixed 200000-subset "
                "bound; inclusion-minimality remains verified"
            ),
        }
    checked = 0
    for size in range(1, support_size):
        for indices in combinations(range(len(system.rows)), size):
            checked += 1
            if _is_inconsistent(_subsystem(system, indices)):
                raise AssertionError("a smaller inconsistency witness exists")
    return {
        "certified": True,
        "minimum_support_size": support_size,
        "smaller_subsets_checked": checked,
    }


def verify_inconsistency_witness(
    system: DecisionSystem,
    witness: Mapping[int, int],
) -> dict[str, Any]:
    columns, rhs = _left_dot_columns(system, witness)
    return {
        "verified": not columns and bool(rhs),
        "nonzero_column_sums": len(columns),
        "rhs_dot": fraction_record(rhs),
        "support_size": sum(bool(value) for value in witness.values()),
    }


def _witness_document(
    system: DecisionSystem,
    witness: Mapping[int, int],
    minimization: Mapping[str, Any],
) -> dict[str, Any]:
    verification = verify_inconsistency_witness(system, witness)
    if not verification["verified"]:
        raise AssertionError("inconsistency witness failed exact verification")
    return {
        "multipliers": [
            {
                "row": row_index,
                "d": system.row_labels[row_index][0],
                "composition": list(system.row_labels[row_index][1]),
                "multiplier": str(multiplier),
            }
            for row_index, multiplier in sorted(witness.items())
            if multiplier
        ],
        "dimensions_present": sorted(
            {system.row_labels[index][0] for index, value in witness.items() if value}
        ),
        "verification": verification,
        "support_minimization": dict(minimization),
    }


def _solution_document(
    system: DecisionSystem,
    *,
    raw_system: DecisionSystem,
) -> dict[str, Any]:
    elimination = exact_eliminate(system)
    if elimination.status != "consistent" or elimination.solution is None:
        raise ValueError("cannot produce a solution for an inconsistent system")
    verification = verify_solution(system, elimination.solution)
    if not verification["verified"]:
        raise AssertionError("exact cumulative solution has nonzero residual")
    raw_verification = verify_solution(raw_system, elimination.solution)
    if not raw_verification["verified"]:
        raise AssertionError("exact cumulative solution fails a raw equation")
    per_dimension = []
    for d in raw_system.dimensions:
        indices = tuple(
            index
            for index, label in enumerate(raw_system.row_labels)
            if label[0] == d
        )
        nonzero_residuals = sum(
            evaluate_sparse_row(raw_system.rows[index], elimination.solution)
            != raw_system.rhs[index]
            for index in indices
        )
        per_dimension.append(
            {
                "d": d,
                "n_rows": len(indices),
                "n_nonzero_residuals": nonzero_residuals,
            }
        )
    return {
        "method": "exact sparse echelon solve with every free coefficient set to zero",
        "nonzero_coefficients": [
            {
                "column": index,
                "name": system.parameter_names[index],
                "value": fraction_record(value),
            }
            for index, value in enumerate(elimination.solution)
            if value
        ],
        "verification": raw_verification,
        "deduplicated_verification": verification,
        "per_dimension_residuals": per_dimension,
    }


def run_progressive_scan() -> dict[str, Any]:
    """Run the bounded cumulative equality scan and return exact evidence."""
    relation = d4_conservation_relation()
    blocks: list[DecisionSystem] = []
    prefixes: list[dict[str, Any]] = []
    previous_rank = 0
    first_inconsistent_dimension: int | None = None
    final_raw: DecisionSystem | None = None
    final_deduplicated: DecisionSystem | None = None
    for d in range(MINIMUM_DIMENSION, MAXIMUM_DIMENSION + 1):
        block = build_dimension_system(d)
        blocks.append(block)
        raw = stack_systems(tuple(blocks))
        deduplication = deduplicate_system(raw)
        deduplicated = deduplication.system
        coefficient_rank, augmented_rank = system_ranks(deduplicated)
        new_deduplicated = sum(
            raw.row_labels[index][0] == d
            for index in deduplication.retained_raw_rows
        )
        prefixes.append(
            {
                "maximum_dimension": d,
                "dimensions": list(raw.dimensions),
                "shared_parameter_count": len(raw.parameter_names),
                "dimension_raw_equations": len(block.rows),
                "dimension_new_deduplicated_equations": new_deduplicated,
                "cumulative_raw_equations": len(raw.rows),
                "cumulative_deduplicated_equations": len(deduplicated.rows),
                "dimension_edges": block.n_edges,
                "cumulative_edges": raw.n_edges,
                "coefficient_rank": coefficient_rank,
                "augmented_rank": augmented_rank,
                "nullity": len(raw.parameter_names) - coefficient_rank,
                "new_independent_constraints_from_dimension": (
                    coefficient_rank - previous_rank
                ),
                "raw_hashes": system_hashes(raw),
                "deduplicated_hashes": system_hashes(deduplicated),
            }
        )
        previous_rank = coefficient_rank
        final_raw = raw
        final_deduplicated = deduplicated
        if augmented_rank > coefficient_rank:
            first_inconsistent_dimension = d
            break
    if final_raw is None or final_deduplicated is None:
        raise AssertionError("scan did not construct a prefix")

    result: dict[str, Any] = {
        "schema": SCAN_SCHEMA,
        "checkpoint_base": CHECKPOINT_BASE,
        "scope": {
            "minimum_dimension": MINIMUM_DIMENSION,
            "maximum_authorized_dimension": MAXIMUM_DIMENSION,
            "largest_dimension_constructed": final_raw.dimensions[-1],
            "shared_parameter_count": len(final_raw.parameter_names),
            "single_shared_coefficient_vector": True,
            "nonnegativity_optimization_run": False,
            "manual_features_appended": [],
            "dimensions_above_10_constructed": False,
        },
        "d4_left_nullspace_relation": relation,
        "deduplication": (
            "complete augmented equations are canonicalized up to nonzero "
            "rational scale; one first-occurring representative is retained"
        ),
        "prefixes": prefixes,
        "first_inconsistent_dimension": first_inconsistent_dimension,
    }
    if first_inconsistent_dimension is not None:
        initial_witness = _extract_primitive_witness(final_deduplicated)
        witness, minimization = inclusion_minimize_witness(
            final_deduplicated, initial_witness
        )
        minimization = dict(minimization)
        minimization["minimum_cardinality_check"] = (
            certify_minimum_cardinality_if_feasible(
                final_deduplicated, witness
            )
        )
        result["decision"] = "inconsistent"
        result["inconsistency_witness"] = _witness_document(
            final_deduplicated, witness, minimization
        )
        result["stopping_rule"] = (
            "stopped at the first cumulative prefix with augmented rank "
            "strictly larger than coefficient rank"
        )
    else:
        result["decision"] = "consistent_through_d10"
        result["solution"] = _solution_document(
            final_deduplicated,
            raw_system=final_raw,
        )
        final_increment = prefixes[-1]["new_independent_constraints_from_dimension"]
        result["d10_effect"] = {
            "new_independent_constraints": final_increment,
            "interpretation": (
                "d=10 rows are implied by earlier coefficient rows"
                if not final_increment
                else "d=10 rows shrink the preceding affine solution space"
            ),
        }
        result["affine_solution_space_dimension"] = prefixes[-1]["nullity"]
        result["stopping_rule"] = (
            "stopped after the consistent d=4,...,10 prefix before "
            "nonnegativity or any larger dimension"
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
    document = run_progressive_scan()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    _write_json(args.output, document)
    print(json.dumps(document, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
