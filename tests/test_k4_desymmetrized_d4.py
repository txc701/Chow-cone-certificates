"""Exact tests for the bounded d=4 oriented-lift equality gate."""

from fractions import Fraction
import json
from pathlib import Path
import tokenize

from k4_degree4_decision import (
    evaluate_sparse_row,
    exact_eliminate,
    normalized_flow_row,
    parameter_names as old_parameter_names,
    system_ranks,
    verify_solution,
)
from k4_desymmetrized_d4 import (
    build_d4_system,
    coefficient_reflection_permutation,
    correspondence_document,
    correspondence_table,
    decision_document,
    embed_old_coefficients,
    fixed_subspace_dimension,
    lifted_normalized_flow_row,
    lifted_parameter_names,
    lifted_witness_row,
    recover_old_coefficients,
    reflect_lifted_coefficients,
    run_d4_gate,
    system_document,
)
from k4_feature_analysis import edge_features


def _feature_signature(feature):
    return (
        feature.peel_width,
        feature.peel_side,
        feature.z,
        feature.L,
        feature.R,
        feature.VL,
        feature.VR,
        feature.QL,
        feature.QR,
    )


def test_complete_deduplicated_lift_and_reversal_correspondence():
    old_names = old_parameter_names()
    new_names = lifted_parameter_names()
    table = correspondence_table()
    permutation = coefficient_reflection_permutation()

    assert len(old_names) == 156
    assert len(new_names) == 276
    assert len(set(new_names)) == 276
    assert len(table) == 156
    assert [record["old_name"] for record in table] == list(old_names)
    assert len(permutation) == 276
    assert tuple(permutation[index] for index in permutation) == tuple(range(276))
    assert fixed_subspace_dimension() == 156

    covered = [
        term["column"] for record in table for term in record["new_terms"]
    ]
    assert len(covered) == 276
    assert sorted(covered) == list(range(276))
    assert sum(len(record["new_terms"]) == 2 for record in table) == 120
    assert sum(len(record["new_terms"]) == 1 for record in table) == 36
    assert all("phi" not in name for name in new_names)

    document = correspondence_document()
    assert document["counts"] == {
        "old_parameters": 156,
        "oriented_basis_per_side_per_peel": 60,
        "balanced_self_reversing_per_peel": 18,
        "new_parameters_per_peel": 138,
        "new_parameters": 276,
        "fixed_subspace_dimension": 156,
    }
    assert document["phi_G_appended"] is False


def test_old_ansatz_is_exactly_the_fixed_coefficient_subspace():
    old = tuple(
        Fraction((index % 11) - 5, (index % 5) + 1)
        for index in range(len(old_parameter_names()))
    )
    lifted = embed_old_coefficients(old)
    assert reflect_lifted_coefficients(lifted) == lifted
    assert recover_old_coefficients(lifted) == old

    for feature in edge_features(4):
        old_row = normalized_flow_row(feature)
        new_row = lifted_normalized_flow_row(feature)
        assert evaluate_sparse_row(old_row, old) == evaluate_sparse_row(
            new_row, lifted
        )
        for old_column, record in enumerate(correspondence_table()):
            reconstructed = sum(
                Fraction(int(term["factor"]))
                * new_row.get(term["column"], Fraction(0))
                for term in record["new_terms"]
            )
            assert reconstructed == old_row.get(old_column, Fraction(0))


def test_d4_equality_system_is_consistent_with_exact_rank_and_residual():
    system = build_d4_system()
    assert system.dimensions == (4,)
    assert len(system.rows) == 5
    assert len(system.parameter_names) == 276
    assert system.n_edges == 5
    assert sum(len(row) for row in system.rows) == 37
    assert system_ranks(system) == (4, 4)

    result = exact_eliminate(system)
    assert result.status == "consistent"
    assert result.rank == 4
    assert result.solution is not None
    assert verify_solution(system, result.solution) == {
        "verified": True,
        "n_rows": 5,
        "n_parameters": 276,
        "n_mismatches": 0,
        "first_mismatch": None,
    }
    assert {
        system.parameter_names[index]: value
        for index, value in enumerate(result.solution)
        if value
    } == {
        "s2:left:invariant:00": Fraction(276),
        "s2:right:invariant:00": Fraction(528),
        "s2:balanced:invariant:00": Fraction(252),
        "s3:balanced:invariant:00": Fraction(144),
    }

    document = decision_document(system)
    assert document["matrix"] == {
        "n_rows": 5,
        "n_columns": 276,
        "n_edges": 5,
        "coefficient_rank": 4,
        "augmented_rank": 4,
        "nullity": 272,
    }
    assert document["equality_status"] == "consistent"
    assert all(
        row["residual"] == {"num": "0", "den": "1"}
        for row in document["solution"]["residuals"]
    )
    assert document["scope"]["nonnegativity_optimization_run"] is False
    assert document["scope"]["holdouts_run"] is False


def test_old_witness_becomes_one_condition_on_ten_untied_columns():
    system = build_d4_system()
    row, rhs = lifted_witness_row(system)
    expected = {}
    indices = (0, 2, 7, 16, 34)
    values = (2, 4, 8, 16, 32)
    by_name = {name: index for index, name in enumerate(system.parameter_names)}
    for basis_index, value in zip(indices, values):
        expected[by_name[f"s2:left:invariant:{basis_index:02d}"]] = Fraction(
            -value
        )
        expected[by_name[f"s2:right:invariant:{basis_index:02d}"]] = Fraction(
            value
        )
    assert row == expected
    assert rhs == 504

    decision = decision_document(system)
    assert decision["old_witness_after_untying"]["n_nonzero_columns"] == 10
    assert decision["old_witness_after_untying"]["rhs"] == {
        "num": "504",
        "den": "1",
    }


def test_phi_and_its_partner_are_not_global_features_but_lie_in_d4_span():
    features8 = {feature.edge: feature for feature in edge_features(8)}
    first_a = features8[((2, 3, 5), 2, 2)]
    first_b = features8[((3, 2, 5), 2, 2)]
    assert _feature_signature(first_a) == _feature_signature(first_b)
    assert (first_a.child[0], first_b.child[0]) == (2, 3)
    assert (first_a.child[-1], first_b.child[-1]) == (3, 3)

    last_a = features8[((5, 2, 3), 0, 2)]
    last_b = features8[((5, 3, 2), 0, 2)]
    assert _feature_signature(last_a) == _feature_signature(last_b)
    assert (last_a.child[0], last_b.child[0]) == (2, 2)
    assert (last_a.child[-1], last_b.child[-1]) == (3, 2)

    names = lifted_parameter_names()
    by_name = {name: index for index, name in enumerate(names)}
    phi_coefficients = [Fraction(0) for _ in names]
    phi_coefficients[by_name["s2:left:invariant:00"]] = Fraction(2)
    phi_coefficients[by_name["s2:right:invariant:00"]] = Fraction(4)
    partner_coefficients = [Fraction(0) for _ in names]
    partner_coefficients[by_name["s2:left:invariant:00"]] = Fraction(4)
    partner_coefficients[by_name["s2:right:invariant:00"]] = Fraction(2)

    for feature in edge_features(4):
        row = lifted_normalized_flow_row(feature)
        is_oriented_width_two = (
            feature.peel_width == 2 and feature.peel_side in {"left", "right"}
        )
        expected_first = Fraction(feature.child[0]) if is_oriented_width_two else 0
        expected_last = Fraction(feature.child[-1]) if is_oriented_width_two else 0
        assert evaluate_sparse_row(row, phi_coefficients) == expected_first
        assert evaluate_sparse_row(row, partner_coefficients) == expected_last


def test_artifacts_are_exact_deterministic_and_d4_only(tmp_path):
    root = tmp_path / "gate"
    first = run_d4_gate(root)
    first_snapshot = {
        path.name: path.read_bytes() for path in sorted(root.iterdir())
    }
    second = run_d4_gate(root)
    second_snapshot = {
        path.name: path.read_bytes() for path in sorted(root.iterdir())
    }
    assert second == first
    assert second_snapshot == first_snapshot
    assert sorted(first_snapshot) == [
        "basis_correspondence.json",
        "decision.json",
        "manifest.json",
        "system.json",
    ]

    system = json.loads(root.joinpath("system.json").read_text(encoding="utf-8"))
    decision = json.loads(
        root.joinpath("decision.json").read_text(encoding="utf-8")
    )
    assert system["dimensions"] == [4]
    assert system["n_rows"] == 5
    assert system["n_columns"] == 276
    assert decision["scope"]["dimensions"] == [4]
    assert decision["equality_status"] == "consistent"


def test_new_gate_source_contains_no_floating_point_or_true_division():
    source = Path(__file__).resolve().parents[1] / "src" / "k4_desymmetrized_d4.py"
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

    system = build_d4_system()
    document = system_document(system)
    assert all(
        isinstance(value, Fraction)
        for row in system.rows
        for value in row.values()
    )
    assert all(
        entry[1].lstrip("-").isdigit() and entry[2].isdigit()
        for row in document["rows"]
        for entry in row["entries"]
    )
