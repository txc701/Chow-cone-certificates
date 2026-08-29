from __future__ import annotations

import inspect
import json
from pathlib import Path

import pytest

from k4_degree5_uniform_gate import (
    affine_space_document,
    build_cumulative_system,
    build_dimension_system,
    build_edge_evaluation_system,
    candidate_edge_representation_system,
    verify_integer_witness,
)
from k4_degree5_quotient_gate import extended_parameter_names
from k4_desymmetrized_d4 import lifted_parameter_names
from k4_degree4_decision import system_ranks


ROOT = Path(__file__).resolve().parents[1]
RESULT_ROOT = ROOT / "results" / "k4_degree5_uniform_gate"


@pytest.fixture(scope="module")
def regenerated_documents() -> tuple[dict, dict]:
    return affine_space_document()


def test_shared_system_has_exact_frozen_shape_and_ranks() -> None:
    system = build_cumulative_system()
    assert system.dimensions == tuple(range(2, 12))
    assert len(system.rows) == 374
    assert len(system.parameter_names) == 524
    assert system.n_edges == 856
    assert system_ranks(system) == (360, 360)


def test_all_dimensions_use_one_symbolic_column_order() -> None:
    names = extended_parameter_names()
    assert len(names) == 524
    assert names[:276] == lifted_parameter_names()
    for d in range(2, 12):
        block = build_dimension_system(d)
        assert block.parameter_names == names
        assert block.dimensions == (d,)


def test_full_affine_space_is_constructed_exactly(
    regenerated_documents: tuple[dict, dict],
) -> None:
    decision, affine = regenerated_documents
    summary = decision["affine_decomposition"]
    assert summary["edge_evaluation_rank"] == 407
    assert summary["edge_invisible_dimension"] == 117
    assert summary["divergence_free_evaluated_flow_dimension"] == 47
    assert summary["total_homogeneous_dimension"] == 164
    assert len(affine["edge_invisible_basis"]) == 117
    assert len(affine["divergence_free_flow_basis"]) == 47
    assert affine["particular_solution"]
    assert summary["particular_verification"]["verified"]
    assert summary["channel_polynomial_verification"]["verified"]


def test_coordinate_section_is_not_misreported_as_nonnegative(
    regenerated_documents: tuple[dict, dict],
) -> None:
    decision, _ = regenerated_documents
    assert decision["affine_decomposition"]["particular_edge_signs"] == {
        "negative": 373,
        "zero": 0,
        "positive": 483,
    }
    assert not decision["scope"]["nonnegativity_of_entire_affine_family_decided"]


def test_uniform_certificate_has_exact_two_edge_feature_image_obstruction(
    regenerated_documents: tuple[dict, dict],
) -> None:
    decision, _ = regenerated_documents
    obstruction = decision["uniform_certificate_relation"]
    assert not obstruction["candidate_is_in_degree5_feature_image"]
    assert (obstruction["coefficient_rank"], obstruction["augmented_rank"]) == (
        407,
        408,
    )
    assert obstruction["primitive_witness_support"] == 2
    assert obstruction["primitive_witness_target_pairing"] == 216
    assert [row["parent"] for row in obstruction["witness"]] == [[2, 4], [4, 2]]
    assert [row["candidate_normalized_flow"] for row in obstruction["witness"]] == [
        ["360", "1"],
        ["144", "1"],
    ]
    system = candidate_edge_representation_system()
    witness = {
        row["row"]: row["multiplier"] for row in obstruction["witness"]
    }
    assert verify_integer_witness(system, witness)["verified"]


def test_saved_artifacts_equal_exact_regeneration(
    regenerated_documents: tuple[dict, dict],
) -> None:
    decision, affine = regenerated_documents
    assert json.loads((RESULT_ROOT / "decision.json").read_text()) == decision
    assert json.loads((RESULT_ROOT / "affine_space.json").read_text()) == affine


def test_edge_system_contains_no_dimension_above_gate() -> None:
    edge_system = build_edge_evaluation_system()
    assert edge_system.dimensions == tuple(range(2, 12))
    assert all(d <= 11 for d, _ in edge_system.row_labels)


def test_gate_source_uses_no_floating_point_linear_algebra() -> None:
    import k4_degree5_uniform_gate

    source = inspect.getsource(k4_degree5_uniform_gate)
    assert "float(" not in source
    assert "numpy" not in source
    assert "scipy" not in source
