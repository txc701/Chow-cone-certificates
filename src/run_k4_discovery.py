"""Deterministic orchestration for the bounded k=4 certificate audit.

The default plan writes:

* one lexicographic certificate for every d=2,...,16;
* all named exact minimum-cost certificates at d=4,6,...,16;
* exact edge-coordinate ranges for d=2,...,10.

No timestamps or timing measurements enter the artifacts.  Every saved
certificate is reread and checked by the standalone verifier before the
manifest is written.  This driver refuses every dimension above 16 and
keeps the deliberately expensive edge-range audit capped at 10.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable

from k4_certificates import (
    COST_PROFILES,
    COST_PROFILE_DEFINITIONS,
    PEEL_WIDTH_MAX,
    SCHEMA as CERTIFICATE_SCHEMA,
    WEIGHT_SCALE,
    allowed_edge_keys,
    certificate_objective_value,
    certificate_document,
    edgewise_ranges,
    min_cost_certificate_document,
)
from k4_feature_analysis import (
    ANSATZ_SCHEMA,
    DEFAULT_HOLDOUT_DIMENSIONS,
    DEFAULT_TRAINING_DIMENSIONS,
    DEFAULT_VALIDATION_DIMENSIONS,
    FEATURE_SCHEMA,
    INTERVAL_WITNESS_SCHEMA,
    ansatz_training_prefix_diagnostics,
    join_feature_records,
    search_ansatz_classes,
    smallest_disjoint_interval_witnesses,
)
from k4_weights import support_w4
from verify_k4_certificates import verify_certificate_file


MAXIMUM_DIMENSION = 16
EDGE_RANGE_MAXIMUM_DIMENSION = 10
DEFAULT_PRIMARY_DIMENSIONS = tuple(range(2, 17))
DEFAULT_OBJECTIVE_DIMENSIONS = (4, 6, 8, 10, 12, 14, 16)
DEFAULT_RANGE_DIMENSIONS = tuple(range(2, 11))
DEFAULT_OBJECTIVES = tuple(sorted(COST_PROFILES))

RANGE_SCHEMA = "chow-cone/k4-edgewise-ranges/v1"
VERIFICATION_SCHEMA = "chow-cone/k4-certificate-verification-summary/v1"
MANIFEST_SCHEMA = "chow-cone/k4-discovery-manifest/v1"
FEATURE_TABLE_SCHEMA = "chow-cone/k4-edge-feature-table/v1"
NONUNIQUENESS_SCHEMA = "chow-cone/k4-nonuniqueness-summary/v1"

RANGE_METHOD_EXPLANATION = (
    "For each allowed edge, remove that edge from the residual network of "
    "the saved lex certificate. Exact integer max-flow rerouting computes "
    "the greatest feasible decrease and increase. Feasible-flow "
    "differences are residual circulations, so the resulting coordinate "
    "minimum and maximum are exact and independent of the baseline solver "
    "tie-breaking."
)
RANGE_CUTOFF_EXPLANATION = (
    "Complete edgewise analysis requires two auxiliary exact max-flow "
    "problems per allowed edge and is intentionally bounded to d<=10."
)


@dataclass(frozen=True)
class DiscoveryPlan:
    """Dimension sets and objectives for one deterministic run."""

    primary_dimensions: tuple[int, ...] = DEFAULT_PRIMARY_DIMENSIONS
    objective_dimensions: tuple[int, ...] = DEFAULT_OBJECTIVE_DIMENSIONS
    range_dimensions: tuple[int, ...] = DEFAULT_RANGE_DIMENSIONS
    objectives: tuple[str, ...] = DEFAULT_OBJECTIVES


def _canonical_dimensions(values: Iterable[int], field: str) -> tuple[int, ...]:
    dimensions = tuple(values)
    for d in dimensions:
        if not isinstance(d, int) or isinstance(d, bool):
            raise ValueError(f"{field} must contain plain integers")
        if d < 2:
            raise ValueError(f"{field} contains d={d}; every d must be at least 2")
        if d > MAXIMUM_DIMENSION:
            raise ValueError(
                f"{field} contains d={d}; dimensions above "
                f"{MAXIMUM_DIMENSION} are forbidden in this stage"
            )
    if len(set(dimensions)) != len(dimensions):
        raise ValueError(f"{field} contains a duplicate dimension")
    return tuple(sorted(dimensions))


def normalize_plan(plan: DiscoveryPlan) -> DiscoveryPlan:
    """Validate bounds and return a canonically ordered plan."""
    primary = _canonical_dimensions(
        plan.primary_dimensions, "primary_dimensions"
    )
    objective_dimensions = _canonical_dimensions(
        plan.objective_dimensions, "objective_dimensions"
    )
    range_dimensions = _canonical_dimensions(
        plan.range_dimensions, "range_dimensions"
    )
    if any(d > EDGE_RANGE_MAXIMUM_DIMENSION for d in range_dimensions):
        raise ValueError(
            "range_dimensions may not exceed the exact edge-range cutoff "
            f"d={EDGE_RANGE_MAXIMUM_DIMENSION}"
        )
    if not set(objective_dimensions).issubset(primary):
        raise ValueError("objective_dimensions must be a subset of primary_dimensions")
    if not set(range_dimensions).issubset(primary):
        raise ValueError("range_dimensions must be a subset of primary_dimensions")

    objectives = tuple(plan.objectives)
    if len(set(objectives)) != len(objectives):
        raise ValueError("objectives contains a duplicate name")
    unknown = set(objectives) - set(COST_PROFILES)
    if unknown:
        raise ValueError(
            f"unknown objective(s): {sorted(unknown)}; expected names from "
            f"{sorted(COST_PROFILES)}"
        )
    return DiscoveryPlan(
        primary_dimensions=primary,
        objective_dimensions=objective_dimensions,
        range_dimensions=range_dimensions,
        objectives=tuple(sorted(objectives)),
    )


def _write_json(path: Path, document: Any) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")


def _write_json_lines(path: Path, records: Iterable[dict[str, Any]]) -> int:
    """Write deterministic compact JSON Lines and return the row count."""
    count = 0
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        for record in records:
            json.dump(record, stream, sort_keys=True, separators=(",", ":"))
            stream.write("\n")
            count += 1
    return count


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _relative(path: Path, output_dir: Path) -> str:
    return path.relative_to(output_dir).as_posix()


def _source_provenance() -> list[dict[str, str]]:
    """Hash every local source module needed to reproduce the artifacts."""
    source_dir = Path(__file__).resolve().parent
    names = (
        "dinic.py",
        "k4_certificates.py",
        "k4_feature_analysis.py",
        "k4_weights.py",
        "min_cost_flow.py",
        "run_k4_discovery.py",
        "support.py",
        "verify_k4_certificates.py",
    )
    return [
        {"path": f"src/{name}", "sha256": _sha256(source_dir.joinpath(name))}
        for name in names
    ]


def _sparse_flow(document: dict[str, Any]) -> dict[tuple, int]:
    return {
        (tuple(parent), block, left): int(flow)
        for parent, block, left, flow in document["edges"]
    }


def _range_mapping(document: dict[str, Any]) -> dict[tuple, dict[str, Any]]:
    """Decode a persisted exact-range document into canonical edge keys."""
    return {
        (tuple(row["parent"]), row["block"], row["left"]): row
        for row in document["edges"]
    }


def _rank_cut_flows(d: int, sparse_flow: dict[tuple, int]) -> dict[int, int]:
    """Return the total flow across every block-count cut."""
    cuts: dict[int, int] = {}
    for parent, block, left in allowed_edge_keys(d):
        rank = len(parent)
        cuts[rank] = cuts.get(rank, 0) + sparse_flow.get(
            (parent, block, left), 0
        )
    return cuts


def _forced_rank_cut_flows(d: int) -> dict[int, int]:
    """Derive rank-cut flows from divergence alone.

    Every cover edge raises the number of blocks by one.  Summing divergence
    over nodes with at most ``rank`` blocks therefore fixes the flow across
    that cut in every feasible certificate.
    """
    weights = support_w4(d)
    maximum_rank = max(len(composition) for composition in weights)
    cumulative = 0
    cuts: dict[int, int] = {}
    for rank in range(1, maximum_rank):
        cumulative += sum(
            weight
            for composition, weight in weights.items()
            if len(composition) == rank
        )
        cuts[rank] = cumulative
    return cuts


def _cut_position_potential(composition: tuple[int, ...]) -> int:
    running = 0
    total = 0
    for part in composition[:-1]:
        running += part
        total += running
    return total


def _nonuniqueness_document(
    normalized: DiscoveryPlan,
    primary_documents: dict[int, dict[str, Any]],
    objective_documents: dict[int, dict[str, dict[str, Any]]],
    range_documents: dict[int, dict[str, Any]],
) -> dict[str, Any]:
    """Separate exact invariants from variation among saved certificates."""
    representative_rows = []
    for d in normalized.objective_dimensions:
        documents = {"primary_lex": primary_documents[d]}
        documents.update(
            {
                f"mincost:{objective}": document
                for objective, document in objective_documents[d].items()
            }
        )
        sparse = {name: _sparse_flow(document) for name, document in documents.items()}
        canonical_edges = allowed_edge_keys(d)
        vectors = {
            name: tuple(flow.get(edge, 0) for edge in canonical_edges)
            for name, flow in sparse.items()
        }
        expected_cuts = _forced_rank_cut_flows(d)
        observed_cuts = {
            name: _rank_cut_flows(d, flow) for name, flow in sparse.items()
        }
        if any(cuts != expected_cuts for cuts in observed_cuts.values()):
            raise RuntimeError(f"rank-cut invariant failed at d={d}")
        forced_total_internal = sum(expected_cuts.values())
        forced_added_position = -sum(
            _cut_position_potential(composition) * weight
            for composition, weight in support_w4(d).items()
        )
        forced_reflected_position = (
            (d + 1) * forced_total_internal - forced_added_position
        )
        objective_matrix = {
            name: {
                objective: str(
                    certificate_objective_value(d, flow, objective)
                )
                for objective in normalized.objectives
            }
            for name, flow in sparse.items()
        }
        profile_variation = {}
        for objective in normalized.objectives:
            values = {
                int(row[objective]) for row in objective_matrix.values()
            }
            profile_variation[objective] = {
                "n_distinct_values_among_saved_certificates": len(values),
                "minimum_saved_value": str(min(values)),
                "maximum_saved_value": str(max(values)),
                "constant_across_saved_certificates": len(values) == 1,
            }
        for objective, expected in (
            ("total_internal_flow", forced_total_internal),
            ("added_cut_position", forced_added_position),
            ("reflected_position", forced_reflected_position),
        ):
            if objective in normalized.objectives and any(
                int(row[objective]) != expected
                for row in objective_matrix.values()
            ):
                raise RuntimeError(
                    f"forced objective {objective} failed at d={d}"
                )
        coordinate_values = list(zip(*vectors.values()))
        varying_coordinates = sum(len(set(values)) > 1 for values in coordinate_values)
        representative_rows.append(
            {
                "d": d,
                "certificate_names": list(documents),
                "n_saved_certificates": len(documents),
                "n_distinct_edgewise_vectors": len(set(vectors.values())),
                "n_allowed_edges": len(canonical_edges),
                "n_coordinates_varying_among_saved_certificates": (
                    varying_coordinates
                ),
                "n_coordinates_constant_among_saved_certificates": (
                    len(canonical_edges) - varying_coordinates
                ),
                "objective_values": objective_matrix,
                "objective_sample_variation": profile_variation,
                "forced_rank_cut_flows": {
                    str(rank): str(value)
                    for rank, value in expected_cuts.items()
                },
                "forced_total_internal_flow": str(sum(expected_cuts.values())),
                "forced_added_cut_position": str(forced_added_position),
                "forced_reflected_position": str(forced_reflected_position),
            }
        )

    exact_range_rows = []
    for d in normalized.range_dimensions:
        document = range_documents[d]
        counts = document["classification_counts"]
        exact_range_rows.append(
            {
                "d": d,
                "n_allowed_edges": document["n_allowed_edges"],
                "classification_counts": counts,
                "n_exactly_fixed_coordinates": (
                    counts["fixed_zero"] + counts["fixed_positive"]
                ),
                "n_exactly_variable_coordinates": (
                    counts["optional"] + counts["forced_variable"]
                ),
            }
        )

    return {
        "schema": NONUNIQUENESS_SCHEMA,
        "exact_invariants": {
            "rank_cut_flows": (
                "For every block-count cut, the total crossing flow equals "
                "the cumulative w4 divergence on lower ranks."
            ),
            "total_internal_flow": (
                "The sum of all edge flows is the sum of the forced rank-cut "
                "flows, so the total_internal_flow objective is constant on "
                "the entire feasible set."
            ),
            "added_cut_position": (
                "Writing Phi(c) for the sum of the proper prefix sums of c, "
                "a split at cut j has Phi(child)-Phi(parent)=j. Therefore "
                "sum_e j(e)f(e)=-sum_c Phi(c)w4(c), independent of f."
            ),
            "reflected_position": (
                "This equals (d+1) times total_internal_flow minus "
                "added_cut_position, so it is also fixed on the feasible set."
            ),
            "edge_coordinate_ranges": (
                "For d<=10, every coordinate minimum and maximum is exact; "
                "minimum=maximum is a solver-independent invariant."
            ),
        },
        "sample_warning": (
            "Equality among saved certificates alone is not treated as an "
            "invariant; variation is a valid nonuniqueness witness, while "
            "sampled equality is only descriptive."
        ),
        "representative_dimensions": representative_rows,
        "exact_coordinate_range_dimensions": exact_range_rows,
    }


def _range_document(
    d: int,
    baseline_path: str,
    baseline_document: dict[str, Any],
) -> dict[str, Any]:
    ranges = edgewise_ranges(d, _sparse_flow(baseline_document))
    canonical_edges = allowed_edge_keys(d, edge_order="lex")
    if list(ranges) != canonical_edges:
        raise RuntimeError(f"edge-range order mismatch at d={d}")

    classification_counts = {
        "fixed_zero": 0,
        "fixed_positive": 0,
        "optional": 0,
        "forced_variable": 0,
    }
    rows = []
    for parent, block, left in canonical_edges:
        item = ranges[(parent, block, left)]
        classification_counts[item.classification] += 1
        child = (
            parent[:block]
            + (left, parent[block] - left)
            + parent[block + 1 :]
        )
        rows.append(
            {
                "parent": list(parent),
                "child": list(child),
                "block": block,
                "left": left,
                "minimum": str(item.minimum),
                "current": str(item.current),
                "maximum": str(item.maximum),
                "classification": item.classification,
            }
        )

    if sum(classification_counts.values()) != len(canonical_edges):
        raise RuntimeError(f"edge-range classification count mismatch at d={d}")
    if len(canonical_edges) != baseline_document["n_allowed_edges"]:
        raise RuntimeError(f"edge-range graph size mismatch at d={d}")

    return {
        "schema": RANGE_SCHEMA,
        "d": d,
        "peel_width_max": PEEL_WIDTH_MAX,
        "weight_scale": WEIGHT_SCALE,
        "baseline_certificate": baseline_path,
        "method": {
            "name": "exact residual-circulation edge-coordinate ranges",
            "explanation": RANGE_METHOD_EXPLANATION,
            "arithmetic": "Python arbitrary-precision integers only",
            "natural_edge_upper_bound": "total_supply",
            "auxiliary_problems_per_edge": 2,
            "cutoff": {
                "maximum_dimension": EDGE_RANGE_MAXIMUM_DIMENSION,
                "explanation": RANGE_CUTOFF_EXPLANATION,
            },
        },
        "edge_order": "canonical (parent composition, block, left)",
        "edge_encoding": {
            "minimum": "canonical decimal integer string",
            "current": "canonical decimal integer string",
            "maximum": "canonical decimal integer string",
        },
        "n_allowed_edges": len(canonical_edges),
        "total_supply": baseline_document["total_supply"],
        "classification_counts": classification_counts,
        "edges": rows,
    }


def run_discovery(
    output_dir: str | Path, plan: DiscoveryPlan | None = None
) -> dict[str, Any]:
    """Execute a bounded plan and return the written manifest document."""
    normalized = normalize_plan(plan or DiscoveryPlan())
    root = Path(output_dir)
    primary_dir = root.joinpath("primary")
    objective_dir = root.joinpath("objectives")
    range_dir = root.joinpath("ranges")
    feature_dir = root.joinpath("features")
    primary_dir.mkdir(parents=True, exist_ok=True)
    objective_dir.mkdir(parents=True, exist_ok=True)
    range_dir.mkdir(parents=True, exist_ok=True)
    feature_dir.mkdir(parents=True, exist_ok=True)

    artifact_records: list[dict[str, Any]] = []
    verification_records: list[dict[str, Any]] = []
    primary_documents: dict[int, dict[str, Any]] = {}
    objective_documents: dict[int, dict[str, dict[str, Any]]] = {}
    range_documents: dict[int, dict[str, Any]] = {}

    def record_certificate(
        path: Path,
        kind: str,
        d: int,
        document: dict[str, Any],
        objective: str | None = None,
    ) -> None:
        _write_json(path, document)
        # Deliberately reread from disk through the independent implementation.
        verification = verify_certificate_file(path)
        if not verification.get("verified"):
            raise RuntimeError(f"standalone verification failed for {path}")
        relative = _relative(path, root)
        digest = _sha256(path)
        artifact = {
            "path": relative,
            "sha256": digest,
            "kind": kind,
            "d": d,
            "schema": CERTIFICATE_SCHEMA,
        }
        verification_record = {
            "path": relative,
            "sha256": digest,
            "kind": kind,
            "d": d,
            "verification": verification,
        }
        if objective is not None:
            artifact["objective"] = objective
            verification_record["objective"] = objective
        artifact_records.append(artifact)
        verification_records.append(verification_record)

    for d in normalized.primary_dimensions:
        document = certificate_document(d, edge_order="lex")
        path = primary_dir.joinpath(f"d{d:02d}_lex.json")
        record_certificate(path, "primary_certificate", d, document)
        primary_documents[d] = document

    for d in normalized.objective_dimensions:
        objective_documents[d] = {}
        for objective in normalized.objectives:
            document = min_cost_certificate_document(d, objective)
            path = objective_dir.joinpath(f"d{d:02d}_{objective}.json")
            record_certificate(
                path,
                "minimum_cost_certificate",
                d,
                document,
                objective=objective,
            )
            objective_documents[d][objective] = document

    for d in normalized.range_dimensions:
        baseline_path = f"primary/d{d:02d}_lex.json"
        document = _range_document(
            d,
            baseline_path=baseline_path,
            baseline_document=primary_documents[d],
        )
        path = range_dir.joinpath(f"d{d:02d}_ranges.json")
        _write_json(path, document)
        range_documents[d] = document
        artifact_records.append(
            {
                "path": _relative(path, root),
                "sha256": _sha256(path),
                "kind": "exact_edgewise_ranges",
                "d": d,
                "schema": RANGE_SCHEMA,
            }
        )

    feature_file_rows = []
    for d in normalized.primary_dimensions:
        certificates = {"primary_lex": _sparse_flow(primary_documents[d])}
        if d in objective_documents:
            certificates.update(
                {
                    f"mincost:{objective}": _sparse_flow(document)
                    for objective, document in objective_documents[d].items()
                }
            )
        ranges = (
            _range_mapping(range_documents[d]) if d in range_documents else None
        )
        records = join_feature_records(d, certificates, ranges)
        path = feature_dir.joinpath(f"d{d:02d}_features.jsonl")
        n_rows = _write_json_lines(path, records)
        if n_rows != len(allowed_edge_keys(d)):
            raise RuntimeError(f"feature row count mismatch at d={d}")
        relative = _relative(path, root)
        feature_file_rows.append(
            {
                "d": d,
                "path": relative,
                "n_rows": n_rows,
                "certificate_columns": sorted(certificates),
                "includes_exact_edge_ranges": ranges is not None,
            }
        )
        artifact_records.append(
            {
                "path": relative,
                "sha256": _sha256(path),
                "kind": "exact_edge_feature_table",
                "d": d,
                "schema": FEATURE_TABLE_SCHEMA,
            }
        )

    feature_schema = {
        "schema": FEATURE_TABLE_SCHEMA,
        "row_schema": FEATURE_SCHEMA,
        "format": "UTF-8 JSON Lines; one canonical allowed edge per line",
        "ordering": "dimension file, then (parent composition, block, left)",
        "integer_arithmetic": (
            "All JSON integer fields were produced with Python "
            "arbitrary-precision integers."
        ),
        "rational_encoding": {
            "shape": {"num": "integer numerator", "den": "positive integer denominator"},
            "normalization": "lowest terms with positive denominator",
        },
        "flow_normalization": "h(parent->child) = flow / G(child)",
        "zero_coordinates": (
            "Every allowed edge is present; omitted sparse-certificate edges "
            "appear here with flow zero."
        ),
        "range_fields": (
            "Exact minimum/current/maximum fields occur precisely for d<=10."
        ),
        "files": feature_file_rows,
    }
    feature_schema_path = feature_dir.joinpath("schema.json")
    _write_json(feature_schema_path, feature_schema)
    artifact_records.append(
        {
            "path": _relative(feature_schema_path, root),
            "sha256": _sha256(feature_schema_path),
            "kind": "feature_table_schema",
            "schema": FEATURE_TABLE_SCHEMA,
        }
    )

    nonuniqueness = _nonuniqueness_document(
        normalized,
        primary_documents,
        objective_documents,
        range_documents,
    )
    nonuniqueness_path = root.joinpath("nonuniqueness_summary.json")
    _write_json(nonuniqueness_path, nonuniqueness)
    artifact_records.append(
        {
            "path": _relative(nonuniqueness_path, root),
            "sha256": _sha256(nonuniqueness_path),
            "kind": "nonuniqueness_summary",
            "schema": NONUNIQUENESS_SCHEMA,
        }
    )

    ansatz = search_ansatz_classes(
        training_dimensions=DEFAULT_TRAINING_DIMENSIONS,
        validation_dimensions=DEFAULT_VALIDATION_DIMENSIONS,
        holdout_dimensions=DEFAULT_HOLDOUT_DIMENSIONS,
    )
    ansatz["training_prefix_diagnostics"] = ansatz_training_prefix_diagnostics(
        first_dimension=min(DEFAULT_TRAINING_DIMENSIONS),
        last_dimension=max(DEFAULT_TRAINING_DIMENSIONS),
    )
    ansatz_path = root.joinpath("ansatz_results.json")
    _write_json(ansatz_path, ansatz)
    artifact_records.append(
        {
            "path": _relative(ansatz_path, root),
            "sha256": _sha256(ansatz_path),
            "kind": "direct_exact_ansatz_results",
            "schema": ANSATZ_SCHEMA,
        }
    )

    interval_witnesses = smallest_disjoint_interval_witnesses(
        {
            d: _range_mapping(document)
            for d, document in range_documents.items()
        },
        max_d=EDGE_RANGE_MAXIMUM_DIMENSION,
    )
    witness_path = root.joinpath("interval_witnesses.json")
    _write_json(witness_path, interval_witnesses)
    artifact_records.append(
        {
            "path": _relative(witness_path, root),
            "sha256": _sha256(witness_path),
            "kind": "solver_independent_interval_witnesses",
            "schema": INTERVAL_WITNESS_SCHEMA,
        }
    )

    eventual_interval_witnesses = smallest_disjoint_interval_witnesses(
        {
            d: _range_mapping(document)
            for d, document in range_documents.items()
            if d >= 3
        },
        max_d=EDGE_RANGE_MAXIMUM_DIMENSION,
    )
    eventual_witness_path = root.joinpath("interval_witnesses_d03_d10.json")
    _write_json(eventual_witness_path, eventual_interval_witnesses)
    artifact_records.append(
        {
            "path": _relative(eventual_witness_path, root),
            "sha256": _sha256(eventual_witness_path),
            "kind": "solver_independent_interval_witnesses_d_ge_3",
            "schema": INTERVAL_WITNESS_SCHEMA,
        }
    )

    verification_summary = {
        "schema": VERIFICATION_SCHEMA,
        "standalone_verifier": "src/verify_k4_certificates.py",
        "all_verified": all(
            row["verification"]["verified"] for row in verification_records
        ),
        "n_certificates": len(verification_records),
        "certificates": verification_records,
    }
    if not verification_summary["all_verified"]:
        raise RuntimeError("at least one saved certificate failed verification")
    verification_path = root.joinpath("verification_summary.json")
    _write_json(verification_path, verification_summary)
    artifact_records.append(
        {
            "path": _relative(verification_path, root),
            "sha256": _sha256(verification_path),
            "kind": "verification_summary",
            "schema": VERIFICATION_SCHEMA,
        }
    )

    manifest = {
        "schema": MANIFEST_SCHEMA,
        "artifact_schemas": {
            "ansatz": ANSATZ_SCHEMA,
            "certificate": CERTIFICATE_SCHEMA,
            "edgewise_ranges": RANGE_SCHEMA,
            "edge_feature_row": FEATURE_SCHEMA,
            "edge_feature_table": FEATURE_TABLE_SCHEMA,
            "interval_witness": INTERVAL_WITNESS_SCHEMA,
            "verification_summary": VERIFICATION_SCHEMA,
            "nonuniqueness_summary": NONUNIQUENESS_SCHEMA,
            "manifest": MANIFEST_SCHEMA,
        },
        "plan": {
            "primary_dimensions": list(normalized.primary_dimensions),
            "primary_edge_order": "lex",
            "objective_dimensions": list(normalized.objective_dimensions),
            "objectives": list(normalized.objectives),
            "range_dimensions": list(normalized.range_dimensions),
        },
        "generator_parameters": {
            "maximum_dimension_guard": MAXIMUM_DIMENSION,
            "edge_range_maximum_dimension": EDGE_RANGE_MAXIMUM_DIMENSION,
            "peel_width_max": PEEL_WIDTH_MAX,
            "weight_scale": WEIGHT_SCALE,
            "node_order": "lexicographic compositions",
            "primary_algorithm": "Dinic exact-integer max flow",
            "objective_algorithm": (
                "successive-shortest-augmenting-path exact-integer "
                "minimum-cost maximum flow"
            ),
            "objective_definitions": {
                name: COST_PROFILE_DEFINITIONS[name]
                for name in normalized.objectives
            },
            "ansatz_split": {
                "training_dimensions": list(DEFAULT_TRAINING_DIMENSIONS),
                "validation_dimensions": list(DEFAULT_VALIDATION_DIMENSIONS),
                "holdout_dimensions": list(DEFAULT_HOLDOUT_DIMENSIONS),
            },
            "ansatz_method": (
                "direct exact normalized-divergence equations over Fraction; "
                "certificate values are not fitted"
            ),
            "range_method": RANGE_METHOD_EXPLANATION,
            "json_encoding": (
                "UTF-8, indent=2, sorted object keys, LF newline; unbounded "
                "flows and range endpoints encoded as decimal strings"
            ),
        },
        "source_provenance": _source_provenance(),
        "n_files_hashed": len(artifact_records),
        "files": artifact_records,
        "manifest_self_hash": (
            "omitted because a file cannot contain its own SHA256 digest"
        ),
    }
    _write_json(root.joinpath("manifest.json"), manifest)
    return manifest


def _parse_dimensions(specification: str) -> tuple[int, ...]:
    """Parse comma-separated integers and inclusive ranges such as 2-5,8."""
    if not specification.strip():
        return ()
    values = []
    for token in specification.split(","):
        token = token.strip()
        if not token:
            raise ValueError("empty dimension token")
        if "-" in token:
            fields = token.split("-")
            if len(fields) != 2:
                raise ValueError(f"invalid dimension range: {token!r}")
            start, end = (int(field) for field in fields)
            if start > end:
                raise ValueError(f"descending dimension range: {token!r}")
            values.extend(range(start, end + 1))
        else:
            values.append(int(token))
    return tuple(values)


def _parse_objectives(specification: str) -> tuple[str, ...]:
    if not specification.strip():
        return ()
    return tuple(token.strip() for token in specification.split(","))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--primary-dimensions", default="2-16")
    parser.add_argument("--objective-dimensions", default="4,6,8,10,12,14,16")
    parser.add_argument("--range-dimensions", default="2-10")
    parser.add_argument(
        "--objectives",
        default=",".join(DEFAULT_OBJECTIVES),
        help="comma-separated names; available: " + ",".join(DEFAULT_OBJECTIVES),
    )
    args = parser.parse_args(argv)
    try:
        plan = DiscoveryPlan(
            primary_dimensions=_parse_dimensions(args.primary_dimensions),
            objective_dimensions=_parse_dimensions(args.objective_dimensions),
            range_dimensions=_parse_dimensions(args.range_dimensions),
            objectives=_parse_objectives(args.objectives),
        )
        manifest = run_discovery(args.output_dir, plan=plan)
    except ValueError as error:
        parser.error(str(error))
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
