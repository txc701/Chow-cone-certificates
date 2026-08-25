"""Exact tests for the separate branch-A d=11 decision gate."""

import ast
from fractions import Fraction
from functools import reduce
import inspect
import json
from math import gcd
from pathlib import Path
import tokenize

import pytest

from k4_degree4_decision import DecisionSystem, system_ranks
import k4_desymmetrized_d11_gate as gate
from k4_desymmetrized_scan import (
    build_cumulative_system,
    deduplicate_system,
    system_hashes,
)
from k4_feature_analysis import g_value


D10_HASHES = {
    "matrix_sha256": "3ab29b5c8c4db6251272db846b18748bd4fb2757276e8261ebbab9e0de2c94af",
    "rhs_sha256": "b884de88fcdc4aa29a5ea8b0330d770c295cfeb5d6980f3cd650fc6f0bc0e1a8",
    "system_sha256": "74440aade255dd61367e0671bffdb490cbe9fb4a1af5b7f6e86f2a6de5d58a53",
}
D11_BLOCK_HASHES = {
    "matrix_sha256": "f8f12e50980be7cd373291a670e3238513691d1e9735cebcc578f0bef28c36e4",
    "rhs_sha256": "80e85f7ab8850a099518736a85a9a508eab54d11f5c9d786c5a63ae5b7dbf070",
    "system_sha256": "205ece2143e69f67958dc73fc1fed0056be9440d3d9987b9a7b1906ac9e8665e",
}
CUMULATIVE_D11_HASHES = {
    "matrix_sha256": "bf20120706d3b3974fa0668f56d4058e686fe9afcc57cce61c9e307cbc3b3cee",
    "rhs_sha256": "9dc33fcaf2e446f0adbedcb221659bc8727db67646b288b5c7ca53825fba3397",
    "system_sha256": "831caf0f2d25a1b3591779b487ea807552f969a0b1ef5682190104ce74529d20",
}
D10_ROW_COUNT = 225
D11_ROW_COUNT = 144
CUMULATIVE_ROW_COUNT = 369


@pytest.fixture(scope="module")
def d10_system():
    return build_cumulative_system(10)


@pytest.fixture(scope="module")
def d11_block():
    return gate.build_d11_block()


@pytest.fixture(scope="module")
def cumulative_d11():
    return gate.build_cumulative_d11_system()


@pytest.fixture(scope="module")
def deduplicated_d11(cumulative_d11):
    return deduplicate_system(cumulative_d11)


@pytest.fixture(scope="module")
def regenerated_document():
    """Regenerate once, dynamically forbidding construction of d=12."""
    original = gate._build_extension_block
    constructed_dimensions = []

    def tracked_build(d):
        if d == gate.CONDITIONAL_HOLDOUT_DIMENSION:
            raise AssertionError("branch A must not construct d=12")
        constructed_dimensions.append(d)
        return original(d)

    gate._build_extension_block = tracked_build
    try:
        document = gate.run_d11_gate()
    finally:
        gate._build_extension_block = original
    assert constructed_dimensions == [11]
    return document


def _add_scaled(target, source, scale):
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        elif column in target:
            del target[column]


def _selected_system(system, indices):
    indices = tuple(indices)
    return DecisionSystem(
        dimensions=tuple(
            sorted({system.row_labels[index][0] for index in indices})
        ),
        parameter_names=system.parameter_names,
        row_labels=tuple(system.row_labels[index] for index in indices),
        rows=tuple(system.rows[index] for index in indices),
        rhs=tuple(system.rhs[index] for index in indices),
        n_edges=system.n_edges,
    )


def _called_function_names(function):
    tree = ast.parse(inspect.getsource(function))
    names = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        if isinstance(node.func, ast.Name):
            names.add(node.func.id)
        elif isinstance(node.func, ast.Attribute):
            names.add(node.func.attr)
    return names


def test_frozen_d10_prefix_embeds_exactly_with_hash_preservation(
    d10_system,
    cumulative_d11,
    regenerated_document,
):
    assert d10_system.dimensions == tuple(range(4, 11))
    assert cumulative_d11.dimensions == tuple(range(4, 12))
    assert len(d10_system.rows) == D10_ROW_COUNT
    assert len(cumulative_d11.rows) == CUMULATIVE_ROW_COUNT
    assert cumulative_d11.parameter_names == d10_system.parameter_names
    assert len(cumulative_d11.parameter_names) == 276
    assert cumulative_d11.row_labels[:D10_ROW_COUNT] == d10_system.row_labels
    assert cumulative_d11.rows[:D10_ROW_COUNT] == d10_system.rows
    assert cumulative_d11.rhs[:D10_ROW_COUNT] == d10_system.rhs
    assert system_hashes(d10_system) == D10_HASHES
    assert regenerated_document["frozen_d10_embedding"] == {
        "verified": True,
        "hashes": D10_HASHES,
    }


def test_d11_block_and_cumulative_ranks_counts_and_hashes_are_exact(
    d11_block,
    cumulative_d11,
    deduplicated_d11,
    regenerated_document,
):
    assert d11_block.dimensions == (11,)
    assert len(d11_block.rows) == D11_ROW_COUNT
    assert d11_block.n_edges == 382
    assert system_ranks(d11_block) == (135, 136)
    assert system_hashes(d11_block) == D11_BLOCK_HASHES

    reduced = deduplicated_d11.system
    assert len(cumulative_d11.rows) == CUMULATIVE_ROW_COUNT
    assert cumulative_d11.n_edges == 853
    assert len(reduced.rows) == CUMULATIVE_ROW_COUNT
    assert deduplicated_d11.retained_raw_rows == tuple(
        range(CUMULATIVE_ROW_COUNT)
    )
    assert deduplicated_d11.raw_to_deduplicated == tuple(
        range(CUMULATIVE_ROW_COUNT)
    )
    assert system_ranks(reduced) == (261, 262)
    assert system_hashes(reduced) == CUMULATIVE_D11_HASHES

    assert regenerated_document["d11_block"] == {
        "raw_rows": 144,
        "n_edges": 382,
        "coefficient_rank": 135,
        "augmented_rank": 136,
        "left_nullity": 9,
        "augmented_left_nullity": 8,
        "equality_status": "inconsistent",
        "hashes": D11_BLOCK_HASHES,
    }
    summary = regenerated_document["cumulative_d11"]
    assert summary["raw_rows"] == 369
    assert summary["deduplicated_rows"] == 369
    assert summary["duplicates_removed"] == 0
    assert summary["n_edges"] == 853
    assert summary["coefficient_rank"] == 261
    assert summary["augmented_rank"] == 262
    assert summary["nullity"] == 15
    assert summary["raw_left_nullity"] == 108
    assert summary["deduplicated_left_nullity"] == 108
    assert summary["augmented_left_nullity"] == 107
    assert summary["compatible_nonconservation_left_nullity"] == 99
    assert summary["new_independent_constraints_from_d11"] == 44
    assert summary["previous_affine_dimension"] == 59
    assert summary["coefficient_direction_dimension_reduction"] == 44
    assert "affine_dimension_reduction" not in summary
    assert summary["hashes"] == CUMULATIVE_D11_HASHES


def test_primitive_d11_only_witness_is_independently_exact(
    cumulative_d11,
    regenerated_document,
):
    witness_document = regenerated_document["inconsistency_witness"]
    records = witness_document["primitive_integer_multipliers"]
    multipliers = {record["row"]: int(record["multiplier"]) for record in records}

    assert len(records) == len(multipliers) == 103
    assert witness_document["dimensions_present"] == [11]
    assert witness_document["primitive_integer_normalization"] == {
        "gcd_of_absolute_multipliers": "1",
        "orientation": "positive target pairing",
    }
    assert witness_document["relation_type"] == (
        "target-active non-conservation inconsistency relation: unlike every "
        "per-d global conservation relation, its target pairing is nonzero"
    )
    assert all(record["d"] == 11 for record in records)
    assert all(row >= D10_ROW_COUNT for row in multipliers)
    assert reduce(gcd, (abs(value) for value in multipliers.values())) == 1

    column_sums = {}
    rhs_dot = Fraction(0)
    for row_index, multiplier in multipliers.items():
        _add_scaled(
            column_sums,
            cumulative_d11.rows[row_index],
            Fraction(multiplier),
        )
        rhs_dot += multiplier * cumulative_d11.rhs[row_index]
    assert column_sums == {}
    assert rhs_dot > 0
    assert witness_document["verification"] == {
        "verified": True,
        "nonzero_column_sums": 0,
        "rhs_dot": {"num": str(rhs_dot.numerator), "den": "1"},
        "support_size": 103,
    }

    support = _selected_system(cumulative_d11, sorted(multipliers))
    assert system_ranks(support) == (102, 103)
    minimization = witness_document["support_minimization"]
    assert minimization["final_support_size"] == 103
    assert minimization["inclusion_minimal"] is True
    assert minimization["support_coefficient_rank"] == 102
    assert minimization["support_augmented_rank"] == 103
    assert minimization["minimum_cardinality_certified"] is False


def test_all_eight_structural_conservation_relations_have_zero_target(
    cumulative_d11,
    regenerated_document,
):
    expected_support_sizes = (5, 8, 13, 21, 34, 55, 89, 144)
    saved = regenerated_document["structural_conservation_relations"]
    assert len(saved) == 8
    for offset, d in enumerate(range(4, 12)):
        indices = tuple(
            index
            for index, label in enumerate(cumulative_d11.row_labels)
            if label[0] == d
        )
        g_values = tuple(
            g_value(cumulative_d11.row_labels[index][1], d)
            for index in indices
        )
        divisor = reduce(gcd, g_values)
        primitive = tuple(value // divisor for value in g_values)
        column_sums = {}
        target = Fraction(0)
        for row_index, multiplier in zip(indices, primitive):
            _add_scaled(
                column_sums,
                cumulative_d11.rows[row_index],
                Fraction(multiplier),
            )
            target += multiplier * cumulative_d11.rhs[row_index]
        assert len(indices) == expected_support_sizes[offset]
        assert column_sums == {}
        assert target == 0
        assert saved[offset] == {
            "d": d,
            "support_size": expected_support_sizes[offset],
            "G_common_divisor": str(divisor),
            "nonzero_column_sums": 0,
            "target_dot": {"num": "0", "den": "1"},
        }


def test_branch_a_excludes_every_solution_or_d12_artifact(regenerated_document):
    assert regenerated_document["decision_branch"] == "A_inconsistent"
    assert regenerated_document["inconsistency_origin"] == (
        "a d=11-only inconsistency exists"
    )
    assert regenerated_document["cumulative_d11"]["affine_intersection"] == (
        "empty"
    )
    assert regenerated_document["cumulative_d11"][
        "target_active_left_relation_dimension"
    ] == 1
    assert regenerated_document["d12_constructed"] is False
    for forbidden in (
        "particular_solution",
        "nullspace",
        "unique_frozen_coefficient_vector",
        "d12_strict_holdout",
    ):
        assert forbidden not in regenerated_document
    assert regenerated_document["stopping_rule"] == (
        "stop immediately at the d<=11 equality inconsistency without "
        "feature repair or holdout construction"
    )


def test_branch_a_regeneration_exactly_matches_saved_artifact(
    regenerated_document,
):
    repository = Path(__file__).resolve().parents[1]
    artifact = json.loads(
        repository.joinpath(
            "results", "k4_desymmetrized_d11_gate", "decision.json"
        ).read_text(encoding="utf-8")
    )
    assert artifact == regenerated_document
    assert artifact["schema"] == "chow-cone/k4-desymmetrized-d11-gate/v1"
    assert artifact["checkpoint_base"] == (
        "60b2fba4a4034e701ad38e344a4c2568ab834906"
    )


def test_no_float_policy_and_static_d12_no_refit_boundary():
    source = Path(inspect.getsourcefile(gate)).resolve()
    with source.open("rb") as stream:
        tokens = list(tokenize.tokenize(stream.readline))
    for token in tokens:
        if token.type == tokenize.OP:
            assert token.string not in {"/", "/="}
        if token.type == tokenize.NUMBER:
            lowered = token.string.lower()
            assert "." not in lowered
            assert "e" not in lowered
        if token.type == tokenize.NAME:
            assert token.string != "float"

    evaluator_calls = _called_function_names(gate.evaluate_strict_d12_holdout)
    assert evaluator_calls.isdisjoint(
        {
            "exact_eliminate",
            "system_ranks",
            "coefficient_echelon",
            "verify_solution",
            "stack_systems",
            "build_cumulative_d11_system",
            "run_d11_gate",
            "refit",
            "solve",
        }
    )
    run_source = inspect.getsource(gate.run_d11_gate)
    assert run_source.index('result["d12_constructed"] = False') < (
        run_source.index("evaluate_strict_d12_holdout(solution)")
    )
    assert gate.TRAINING_DIMENSION == 11
    assert gate.CONDITIONAL_HOLDOUT_DIMENSION == 12
    for invalid in (10, 13, True, False, 11.0, 12.0, 13.0, "11", None):
        with pytest.raises(ValueError):
            gate._build_extension_block(invalid)
