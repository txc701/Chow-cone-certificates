"""Focused tests for exact k=4 feature and ansatz analysis."""

from fractions import Fraction
import json

import pytest

from k4_certificates import EdgeRange, allowed_edge_keys, edgewise_ranges, solve_certificate
from k4_feature_analysis import (
    ANSATZ_SCHEMA,
    BASIS_COLUMNS,
    FEATURE_SCHEMA,
    INTERVAL_WITNESS_SCHEMA,
    ansatz_training_prefix_diagnostics,
    build_ansatz_system,
    edge_feature_records,
    edge_features,
    fraction_record,
    g_child_parent_ratio,
    join_feature_records,
    s4_simplified,
    search_ansatz_class,
    smallest_disjoint_interval_witnesses,
    solve_fraction_system,
)
from k4_weights import b4_720, s4
from support import support_compositions


def test_s4_simplification_and_closed_g_ratio_are_exact():
    assert b4_720(2) == 240
    assert 15 * (2 + 2) ** 2 - 6 * (2 + 2) == 216
    for d in range(2, 7):
        for composition in support_compositions(d):
            assert s4_simplified(composition, d) == s4(composition)
        for feature in edge_features(d):
            expected = g_child_parent_ratio(
                feature.block_size,
                feature.left_part,
                feature.is_final_block,
            )
            assert feature.ratio == expected
            assert feature.ratio == Fraction(feature.G_child, feature.G_parent)
            assert feature.v_left + feature.v_right - feature.v_block == (
                -2 * feature.left_part * feature.right_part
            )


def test_every_allowed_edge_has_complete_json_feature_schema():
    d = 6
    features = edge_features(d)
    records = edge_feature_records(d)
    assert [feature.edge for feature in features] == allowed_edge_keys(d)
    assert len(records) == len(allowed_edge_keys(d))
    required = {
        "schema",
        "edge_id",
        "d",
        "parent",
        "child",
        "peel_width",
        "peel_side",
        "affected_block",
        "block_position",
        "parent_prefix_sums",
        "L",
        "R",
        "VL",
        "VR",
        "QL",
        "QR",
        "V",
        "Q2",
        "cross",
        "S4_parent",
        "S4_child",
        "G_parent",
        "G_child",
        "G_child_over_parent",
    }
    for record in records:
        assert required <= set(record)
        assert record["schema"] == FEATURE_SCHEMA
        assert record["peel_width"] <= 3
        assert record["G_child_over_parent"]["den"] > 0
    # This catches accidental tuple/Fraction leakage from the exact internals.
    json.dumps(records, sort_keys=True)


def test_sparse_certificates_and_ranges_join_with_explicit_zeroes():
    d = 4
    lex = solve_certificate(d, edge_order="lex")
    reverse = solve_certificate(d, edge_order="reverse_lex")
    ranges = edgewise_ranges(d, lex)
    records = join_feature_records(
        d, {"reverse": reverse, "lex": lex}, ranges
    )
    assert len(records) == len(allowed_edge_keys(d))
    assert all(list(record["certificates"]) == ["lex", "reverse"] for record in records)
    assert any(
        certificate["flow"] == 0
        for record in records
        for certificate in record["certificates"].values()
    )
    for record in records:
        denominator = record["G_child"]
        for certificate in record["certificates"].values():
            assert certificate["normalized_flow"] == fraction_record(
                Fraction(certificate["flow"], denominator)
            )
        edge_range = record["edge_range"]
        assert edge_range["normalized_minimum"] == fraction_record(
            Fraction(edge_range["minimum"], denominator)
        )
        assert edge_range["normalized_maximum"] == fraction_record(
            Fraction(edge_range["maximum"], denominator)
        )
    json.dumps(records, sort_keys=True)


def test_certificate_normalization_has_the_claimed_exact_divergence_sign():
    d = 6
    sparse = solve_certificate(d)
    divergence = {
        composition: Fraction(0) for composition in support_compositions(d)
    }
    for feature in edge_features(d):
        normalized = Fraction(sparse.get(feature.edge, 0), feature.G_child)
        divergence[feature.parent] += feature.ratio * normalized
        divergence[feature.child] -= normalized
    assert divergence == {
        composition: Fraction(s4(composition))
        for composition in support_compositions(d)
    }


def test_fraction_gaussian_elimination_reports_all_three_cases():
    unique = solve_fraction_system([[1, 1], [1, -1]], [3, 1])
    assert unique.status == "unique"
    assert unique.solution == (Fraction(2), Fraction(1))
    assert unique.free_columns == ()

    inconsistent = solve_fraction_system([[1], [1]], [1, 2])
    assert inconsistent.status == "inconsistent"
    assert inconsistent.solution is None
    assert inconsistent.inconsistent_row is not None

    underdetermined = solve_fraction_system([[1, 1]], [1])
    assert underdetermined.status == "underdetermined"
    assert underdetermined.free_columns == (1,)
    assert underdetermined.solution == (Fraction(1), Fraction(0))


def test_direct_ansatz_system_and_result_have_frozen_structure_on_small_d():
    system = build_ansatz_system((3,), "P0")
    assert system.basis == "P0"
    assert system.dimensions == (3,)
    assert len(system.row_labels) == len(support_compositions(3))
    assert len(system.matrix) == len(system.rhs)
    assert all(len(row) == len(system.parameter_names) for row in system.matrix)

    result = search_ansatz_class(
        "P0",
        training_dimensions=(3,),
        validation_dimensions=(4,),
        holdout_dimensions=(5,),
    )
    assert result["schema"] == ANSATZ_SCHEMA
    assert result["basis_columns"] == list(BASIS_COLUMNS["P0"])
    assert result["fit"]["status"] == "unique"
    assert result["status"] == "validation_failure"
    assert not result["passed"]
    assert set(result["phase_checks"]) == {"training", "validation"}
    assert result["phase_checks"]["training"]["all_nonnegative"]
    assert result["phase_checks"]["training"]["exact_divergence"]
    json.dumps(result, sort_keys=True)

    # The richer class is honestly reported as unidentified on this tiny fit;
    # its canonical free-zero representative is not promoted to a rule.
    rich = search_ansatz_class(
        "P3",
        training_dimensions=(3,),
        validation_dimensions=(4,),
        holdout_dimensions=(5,),
    )
    assert rich["fit"]["status"] == "underdetermined"
    assert rich["status"] == "underdetermined"
    assert not rich["passed"]
    assert rich["coefficients"] is None

    with pytest.raises(ValueError, match="strictly ordered"):
        search_ansatz_class(
            "P0",
            training_dimensions=(3,),
            validation_dimensions=(3,),
            holdout_dimensions=(4,),
        )


def test_training_prefix_diagnostic_stops_at_exact_first_obstruction():
    result = ansatz_training_prefix_diagnostics(
        ("P0",), first_dimension=3, last_dimension=5
    )[0]
    assert result["first_inconsistent_maximum_dimension"] == 4
    assert [step["status"] for step in result["steps"]] == [
        "unique",
        "inconsistent",
    ]


def test_disjoint_normalized_ranges_give_solver_independent_smallest_pair():
    # These edges have the same block-local and prefix signatures but different
    # suffix state.  Synthetic singleton coordinate ranges isolate the witness
    # selection logic from max-flow tie-breaking.
    edge1 = ((6, 2), 0, 2)  # d=6, split the nonfinal 6 as (2,4)
    edge2 = ((6, 4), 0, 2)  # d=8, same local/prefix data
    feature1 = {feature.edge: feature for feature in edge_features(6)}[edge1]
    feature2 = {feature.edge: feature for feature in edge_features(8)}[edge2]
    ranges = {
        6: {edge1: EdgeRange(0, 0, 0, "fixed_zero")},
        8: {
            edge2: EdgeRange(
                feature2.G_child,
                feature2.G_child,
                feature2.G_child,
                "fixed_positive",
            )
        },
    }
    result = smallest_disjoint_interval_witnesses(ranges, max_d=10)
    assert result["schema"] == INTERVAL_WITNESS_SCHEMA
    levels = {row["level"]: row for row in result["levels"]}
    for level in ("block_local", "prefix_state"):
        witness = levels[level]["witness"]
        assert witness is not None
        assert witness["first_edge"]["edge_id"] == feature1.edge_id
        assert witness["second_edge"]["edge_id"] == feature2.edge_id
        assert witness["first_normalized_interval"]["maximum"] == {
            "num": 0,
            "den": 1,
        }
        assert witness["second_normalized_interval"]["minimum"] == {
            "num": 1,
            "den": 1,
        }
        assert witness["gap"] == {"num": 1, "den": 1}
    assert levels["two_sided_state"]["witness"] is None
    assert levels["moment_state"]["witness"] is None
    json.dumps(result, sort_keys=True)
