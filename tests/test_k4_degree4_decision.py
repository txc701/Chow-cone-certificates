"""Focused tests for the bounded k=4 degree-four decision experiment."""

from fractions import Fraction
import json
from pathlib import Path

import pytest

from k4_degree4_decision import (
    DecisionSystem,
    TRAINING_DIMENSIONS,
    balanced_invariant_basis,
    basis_document,
    build_decision_system,
    exact_eliminate,
    evaluate_sparse_row,
    mirror_edge_key,
    mirror_exponent,
    mirror_polynomial,
    mirror_values,
    normalized_flow_row,
    parameter_names,
    primitive_integer_witness,
    raw_monomials,
    symmetry_basis,
    system_ranks,
    verify_integer_witness,
    verify_solution,
    weighted_degree,
)
from k4_feature_analysis import edge_features
from k4_weights import s4
from run_k4_degree4_decision import run_decision
from support import support_compositions
from verify_k4_degree4_decision import (
    DecisionVerificationError,
    verify_artifact_directory,
    verify_basis,
)


def _negate(polynomial):
    return tuple((exponent, -coefficient) for exponent, coefficient in polynomial)


def test_complete_weighted_basis_and_every_symmetry_type():
    basis = symmetry_basis()
    assert len(basis.raw) == 60
    assert len(basis.invariant) == 35
    assert len(basis.anti_invariant) == 25
    assert len(balanced_invariant_basis()) == 18
    assert len(parameter_names()) == 156
    assert len(set(basis.raw)) == len(basis.raw)
    assert set(basis.raw) == set(raw_monomials())

    assert [
        sum(weighted_degree(exponent) == degree for exponent in basis.raw)
        for degree in range(5)
    ] == [1, 3, 8, 16, 32]
    assert [
        sum(
            weighted_degree(polynomial[0][0]) == degree
            for polynomial in basis.invariant
        )
        for degree in range(5)
    ] == [1, 2, 5, 9, 18]
    assert [
        sum(
            weighted_degree(polynomial[0][0]) == degree
            for polynomial in basis.anti_invariant
        )
        for degree in range(5)
    ] == [0, 1, 3, 7, 14]

    for exponent in basis.raw:
        assert mirror_exponent(mirror_exponent(exponent)) == exponent
        assert weighted_degree(exponent) <= 4
    for polynomial in basis.invariant:
        assert mirror_polynomial(polynomial) == polynomial
    for polynomial in basis.anti_invariant:
        assert mirror_polynomial(polynomial) == _negate(polynomial)
    assert all(
        any(exponent[0] == 0 for exponent, _ in polynomial)
        for polynomial in balanced_invariant_basis()
    )

    document = basis_document()
    assert verify_basis(document)["verified"]
    assert document["parameter_count"] == 156


def test_composition_reversal_and_ansatz_rows_are_exactly_equivariant():
    side_mirror = {"left": "right", "right": "left", "balanced": "balanced"}
    for d in range(2, 9):
        features = edge_features(d)
        by_edge = {feature.edge: feature for feature in features}
        for feature in features:
            mirrored = by_edge[mirror_edge_key(feature)]
            assert mirror_edge_key(mirrored) == feature.edge
            values = (
                feature.z,
                feature.L,
                feature.R,
                feature.VL,
                feature.VR,
                feature.QL,
                feature.QR,
            )
            mirrored_values = (
                mirrored.z,
                mirrored.L,
                mirrored.R,
                mirrored.VL,
                mirrored.VR,
                mirrored.QL,
                mirrored.QR,
            )
            assert mirrored_values == mirror_values(values)
            assert mirrored.peel_side == side_mirror[feature.peel_side]
            assert normalized_flow_row(mirrored) == normalized_flow_row(feature)

            alpha_parent = Fraction(feature.parent[0], feature.parent[-1])
            alpha_child = Fraction(feature.child[0], feature.child[-1])
            assert mirrored.ratio == feature.ratio * alpha_child / alpha_parent


def test_sparse_elimination_extracts_a_machine_checkable_witness():
    system = DecisionSystem(
        dimensions=(2,),
        parameter_names=("x",),
        row_labels=((2, (4,)), (2, (2, 2))),
        rows=({0: Fraction(1)}, {0: Fraction(1)}),
        rhs=(Fraction(1), Fraction(2)),
        n_edges=0,
    )
    result = exact_eliminate(system)
    assert result.status == "inconsistent"
    integer_witness, rhs = primitive_integer_witness(result.witness, system.rhs)
    assert integer_witness == {0: -1, 1: 1}
    assert rhs == 1
    assert verify_integer_witness(system, integer_witness) == {
        "verified": True,
        "n_nonzero_multipliers": 2,
        "n_nonzero_column_sums": 0,
        "rhs_sum": {"num": "1", "den": "1"},
    }


def test_actual_smallest_obstruction_and_preceding_solution_are_exact():
    preceding = build_decision_system((2, 3))
    preceding_result = exact_eliminate(preceding)
    assert preceding_result.status == "consistent"
    assert preceding_result.rank == 2
    assert verify_solution(preceding, preceding_result.solution)["verified"]

    obstructed = build_decision_system((2, 3, 4))
    result = exact_eliminate(obstructed)
    assert result.status == "inconsistent"
    assert system_ranks(obstructed) == (5, 6)
    witness, rhs = primitive_integer_witness(result.witness, obstructed.rhs)
    assert rhs == 504
    assert {
        (obstructed.row_labels[index], multiplier)
        for index, multiplier in witness.items()
    } == {
        ((4, (2, 2, 2)), -1),
        ((4, (2, 4)), 2),
        ((4, (4, 2)), -2),
    }
    assert verify_integer_witness(obstructed, witness)["verified"]


def test_independent_small_dimension_divergence_uses_out_minus_in_sign():
    coefficients = [Fraction(0) for _ in parameter_names()]
    name_to_index = {name: index for index, name in enumerate(parameter_names())}
    coefficients[name_to_index["s2:oriented:invariant:00"]] = Fraction(300)
    coefficients[name_to_index["s2:balanced:invariant:00"]] = Fraction(240)
    for d in (2, 3):
        divergence = {
            composition: Fraction(0) for composition in support_compositions(d)
        }
        for feature in edge_features(d):
            normalized = evaluate_sparse_row(
                normalized_flow_row(feature), coefficients
            )
            divergence[feature.parent] += feature.ratio * normalized
            divergence[feature.child] -= normalized
        assert divergence == {
            composition: Fraction(s4(composition))
            for composition in support_compositions(d)
        }


def test_full_frozen_system_has_expected_size_and_rank_gap():
    system = build_decision_system(TRAINING_DIMENSIONS)
    assert len(system.rows) == 607
    assert system.n_edges == 1529
    assert len(system.parameter_names) == 156
    assert system_ranks(system) == (155, 156)


def test_runner_is_reproducible_and_standalone_verifier_rejects_corruption(tmp_path):
    root = tmp_path / "decision"
    first = run_decision(root)
    first_snapshot = {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }
    second = run_decision(root)
    second_snapshot = {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }
    assert second == first
    assert second_snapshot == first_snapshot
    verification = verify_artifact_directory(root)
    assert verification["verified"]
    assert verification["witness"]["rhs_sum"] == {"num": "504", "den": "1"}

    witness_path = root / "inconsistency_witness.json"
    witness = json.loads(witness_path.read_text(encoding="utf-8"))
    witness["multipliers"][0]["multiplier"] = "1"
    witness_path.write_text(json.dumps(witness), encoding="utf-8")
    with pytest.raises(DecisionVerificationError, match="inconsistency"):
        verify_artifact_directory(root)


def test_persisted_decision_artifacts_verify_from_the_repository():
    repository = Path(__file__).resolve().parents[1]
    root = repository.joinpath("results", "k4_degree4_decision")
    verification = verify_artifact_directory(root)
    assert verification["verified"]
    assert verification["system"] == {
        "verified": True,
        "dimensions": list(range(2, 13)),
        "n_rows": 607,
        "n_edges": 1529,
        "n_parameters": 156,
    }
