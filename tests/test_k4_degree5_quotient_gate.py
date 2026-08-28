"""Exact d=11-only tests for the weighted-degree-five quotient gate."""

from collections import Counter
from fractions import Fraction
from functools import reduce
import inspect
import json
from math import gcd
from pathlib import Path
import tokenize

import pytest

from k4_degree4_decision import (
    DecisionSystem,
    matrix_rank,
    system_ranks,
    weighted_degree,
)
from k4_desymmetrized_d4 import (
    lifted_normalized_flow_row,
    lifted_parameter_names,
)
import k4_degree5_quotient_gate as gate
from k4_feature_analysis import edge_features, g_value
from k4_desymmetrized_scan import system_hashes


FROZEN_D11_HASHES = {
    "matrix_sha256": "f8f12e50980be7cd373291a670e3238513691d1e9735cebcc578f0bef28c36e4",
    "rhs_sha256": "80e85f7ab8850a099518736a85a9a508eab54d11f5c9d786c5a63ae5b7dbf070",
    "system_sha256": "205ece2143e69f67958dc73fc1fed0056be9440d3d9987b9a7b1906ac9e8665e",
}
DEFINITIONS_HASH = "ca5d7c25e4c4962c23febcbb32be95808d377addf731d281fe180854518847f4"
NEW_MATRIX_HASH = "523bf5753d126abf9aa9b1dd6aee4722eab0f8cc0b333f49ea83f805a2418282"
NEW_MATRIX_SEMANTIC_HASH = (
    "6cafbbb9612d2414f859bba0f807193e586758f6d968d06f23e64d395d332bec"
)
KERNEL_HASH = "4937cf09a5efd75bfac6d2071046513eaf29f20183c2c231038a22f3d212465e"
SIGNATURES_HASH = "f2fd8b257397d9192db56caa0c4ad6c701a830293b010ee81c51fa62c2b685e0"


@pytest.fixture(scope="module")
def symbolic_features():
    return gate.degree_five_features()


@pytest.fixture(scope="module")
def old_system():
    return gate.build_d11_block()


@pytest.fixture(scope="module")
def new_matrix():
    return gate.build_new_degree_five_matrix()


@pytest.fixture(scope="module")
def kernel_data(old_system):
    return gate.left_kernel_data(old_system)


@pytest.fixture(scope="module")
def regenerated_document():
    """Regenerate once while forbidding other dimensions and a full solve."""
    original_edges = gate.edge_features
    original_eliminate = gate.exact_eliminate
    original_matrix_rank = gate.matrix_rank
    original_system_ranks = gate.system_ranks
    original_build_old = gate.build_d11_block
    seen_dimensions = []
    elimination_shapes = []

    def tracked_edges(d):
        if d != 11:
            raise AssertionError("the quotient gate must construct only d=11")
        seen_dimensions.append(d)
        return original_edges(d)

    def guarded_eliminate(system):
        shape = (len(system.rows), len(system.parameter_names))
        elimination_shapes.append(shape)
        if len(system.rows) != 9 or len(system.parameter_names) > 248:
            raise AssertionError("a full expanded coefficient solve was attempted")
        return original_eliminate(system)

    def guarded_matrix_rank(rows):
        materialized = tuple(rows)
        if len(materialized) == 144 and any(
            column >= 276 for row in materialized for column in row
        ):
            raise AssertionError("a full 144x524 rank elimination was attempted")
        return original_matrix_rank(materialized)

    def guarded_system_ranks(system):
        if len(system.parameter_names) > 276:
            raise AssertionError("a full expanded system rank was attempted")
        return original_system_ranks(system)

    def tracked_build_old():
        system = original_build_old()
        if system.dimensions != (11,):
            raise AssertionError("the frozen system is not d=11-only")
        return system

    gate.edge_features = tracked_edges
    gate.exact_eliminate = guarded_eliminate
    gate.matrix_rank = guarded_matrix_rank
    gate.system_ranks = guarded_system_ranks
    gate.build_d11_block = tracked_build_old
    try:
        document = gate.run_degree_five_quotient_gate()
    finally:
        gate.edge_features = original_edges
        gate.exact_eliminate = original_eliminate
        gate.matrix_rank = original_matrix_rank
        gate.system_ranks = original_system_ranks
        gate.build_d11_block = original_build_old
    assert seen_dimensions and set(seen_dimensions) == {11}
    assert elimination_shapes
    assert all(rows == 9 and columns <= 248 for rows, columns in elimination_shapes)
    return document


def _parse_fraction(record):
    return Fraction(int(record["num"]), int(record["den"]))


def _parse_fraction_list(records):
    return tuple(_parse_fraction(record) for record in records)


def _column_signatures(matrix, basis):
    return tuple(
        tuple(
            sum(
                (
                    Fraction(vector[row_index])
                    * matrix.rows[row_index].get(column, Fraction(0))
                    for row_index in range(len(matrix.rows))
                ),
                Fraction(0),
            )
            for vector in basis
        )
        for column in range(len(matrix.parameter_names))
    )


def _target_signature(rhs, basis):
    return tuple(
        sum(
            (
                Fraction(vector[row_index]) * rhs[row_index]
                for row_index in range(len(rhs))
            ),
            Fraction(0),
        )
        for vector in basis
    )


def _signature_system(names, signatures, target):
    return DecisionSystem(
        dimensions=(11,),
        parameter_names=tuple(names),
        row_labels=tuple((11, (coordinate,)) for coordinate in range(9)),
        rows=tuple(
            {
                column: signature[coordinate]
                for column, signature in enumerate(signatures)
                if signature[coordinate]
            }
            for coordinate in range(9)
        ),
        rhs=tuple(target),
        n_edges=0,
    )


def _restricted_columns(system, columns):
    columns = tuple(columns)
    renumber = {column: index for index, column in enumerate(columns)}
    return DecisionSystem(
        dimensions=(11,),
        parameter_names=tuple(system.parameter_names[column] for column in columns),
        row_labels=system.row_labels,
        rows=tuple(
            {
                renumber[column]: value
                for column, value in row.items()
                if column in renumber
            }
            for row in system.rows
        ),
        rhs=system.rhs,
        n_edges=0,
    )


def test_exact_degree5_columns_are_complete_global_and_oriented(
    symbolic_features,
    regenerated_document,
):
    assert len(symbolic_features) == 248
    assert len({feature.name for feature in symbolic_features}) == 248
    assert len({feature.symbolic_key for feature in symbolic_features}) == 248
    assert len(gate.extended_parameter_names()) == 524
    assert gate.extended_parameter_names()[:276] == lifted_parameter_names()
    assert not (
        set(gate.extended_parameter_names()[:276])
        & set(gate.extended_parameter_names()[276:])
    )

    counts = Counter(
        (feature.peel_width, feature.channel, feature.parity)
        for feature in symbolic_features
    )
    for peel in (2, 3):
        for channel in ("left", "right"):
            assert counts[(peel, channel, "invariant")] == 30
            assert counts[(peel, channel, "anti")] == 26
        assert counts[(peel, "balanced", "invariant")] == 12
    for feature in symbolic_features:
        assert all(
            weighted_degree(exponent) == 5
            for exponent, _ in feature.polynomial
        )
        expected_factor = (
            -1
            if feature.channel == "right" and feature.parity == "anti"
            else 1
        )
        assert feature.orientation_factor == expected_factor
        assert feature.oriented_polynomial == tuple(
            (exponent, expected_factor * coefficient)
            for exponent, coefficient in feature.polynomial
        )

    assert gate.verify_feature_nesting() == {
        "verified": True,
        "old_parameters": 276,
        "old_invariant_per_peel": 35,
        "old_anti_per_peel": 25,
        "old_balanced_per_peel": 18,
        "degree5_invariant_per_side_per_peel": 30,
        "degree5_anti_per_side_per_peel": 26,
        "degree5_balanced_per_peel": 12,
    }
    saved = regenerated_document["degree5_symbolic_columns"]
    assert saved["candidate_count"] == 248
    assert saved["globally_deduplicated_count"] == 248
    assert saved["duplicates_removed"] == 0
    assert saved["extended_parameter_count"] == 524
    assert saved["definitions_sha256"] == DEFINITIONS_HASH


def test_old_276_columns_are_an_exact_edgewise_prefix_and_frozen(
    old_system,
    regenerated_document,
):
    assert old_system.dimensions == (11,)
    assert len(old_system.rows) == 144
    assert old_system.n_edges == 382
    assert len(old_system.parameter_names) == 276
    assert system_ranks(old_system) == (135, 136)
    assert system_hashes(old_system) == FROZEN_D11_HASHES

    features = edge_features(11)
    assert len(features) == 382
    for feature in features:
        old_row = lifted_normalized_flow_row(feature)
        extended = gate.extended_normalized_flow_row(feature)
        assert {
            column: value
            for column, value in extended.items()
            if column < 276
        } == old_row
        assert all(column >= 276 for column in extended if column not in old_row)
    assert regenerated_document["frozen_degree4"] == {
        "parameter_count": 276,
        "rank": 135,
        "hashes": FROZEN_D11_HASHES,
    }
    assert regenerated_document["edgewise_old_embedding"] == {
        "verified": True,
        "d": 11,
        "n_edges_checked": 382,
        "old_coordinate_count": 276,
        "old_names_are_exact_prefix": True,
    }


def test_exact_left_kernel_has_conservation_plus_eight_complement_coordinates(
    old_system,
    kernel_data,
    regenerated_document,
):
    basis = kernel_data.basis
    assert len(basis) == 9
    assert all(len(vector) == 144 for vector in basis)
    assert matrix_rank(
        tuple(
            {
                column: Fraction(value)
                for column, value in enumerate(vector)
                if value
            }
            for vector in basis
        )
    ) == 9
    for vector in basis:
        for column in range(276):
            assert sum(
                (
                    Fraction(vector[row])
                    * old_system.rows[row].get(column, Fraction(0))
                    for row in range(144)
                ),
                Fraction(0),
            ) == 0

    g_values = tuple(
        g_value(composition, 11) for _, composition in old_system.row_labels
    )
    divisor = reduce(gcd, g_values)
    conservation = tuple(value // divisor for value in g_values)
    assert basis[0] == conservation
    assert reduce(gcd, conservation) == 1
    anchor = kernel_data.conservation_anchor_row
    assert conservation[anchor] != 0
    assert all(vector[anchor] == 0 for vector in basis[1:])

    saved = regenerated_document["left_kernel"]
    assert saved["dimension"] == 9
    assert saved["basis_rank"] == 9
    assert saved["basis_sha256"] == KERNEL_HASH
    assert saved["conservation_coordinate"] == 0
    assert saved["effective_obstruction_coordinates"] == list(range(1, 9))
    assert saved["conservation_anchor_row"] == anchor == 58
    assert saved["free_row_indices"] == list(kernel_data.free_row_indices)
    assert saved["conservation_verification"] == {
        "verified": True,
        "legal_edges_checked": 382,
        "nonzero_edge_factors": 0,
        "new_columns_with_nonzero_conservation_coordinate": 0,
        "target_conservation_coordinate": {"num": "0", "den": "1"},
    }


def test_all_new_signatures_and_target_are_exact_with_rank_five(
    old_system,
    new_matrix,
    kernel_data,
    regenerated_document,
):
    assert len(new_matrix.rows) == 144
    assert len(new_matrix.parameter_names) == 248
    signatures = _column_signatures(new_matrix, kernel_data.basis)
    target = _target_signature(old_system.rhs, kernel_data.basis)
    saved = regenerated_document["cokernel_signatures"]

    assert tuple(
        record["name"] for record in saved["new_column_signatures"]
    ) == new_matrix.parameter_names
    assert tuple(
        _parse_fraction_list(record["signature"])
        for record in saved["new_column_signatures"]
    ) == signatures
    assert _parse_fraction_list(saved["target_signature"]) == target
    assert all(signature[0] == 0 for signature in signatures)
    assert target[0] == 0

    signature_system = _signature_system(
        new_matrix.parameter_names, signatures, target
    )
    assert system_ranks(signature_system) == (5, 5)
    assert saved["new_signature_rank"] == 5
    assert saved["augmented_signature_rank"] == 5
    assert saved["evaluation_rank_modulo_old_columns"] == 5
    assert saved["zero_signature_count"] == 128
    assert saved["distinct_signature_count"] == 119
    assert saved["coordinate_nonzero_column_counts"] == [
        0, 0, 0, 120, 120, 120, 120, 120, 120
    ]
    assert saved["signatures_sha256"] == SIGNATURES_HASH
    assert regenerated_document["d11_new_column_matrix"] == {
        "n_rows": 144,
        "n_columns": 248,
        "matrix_sha256": NEW_MATRIX_HASH,
        "semantic_sha256": NEW_MATRIX_SEMANTIC_HASH,
    }


def test_five_column_certificate_is_exact_and_inclusion_minimal(
    old_system,
    new_matrix,
    kernel_data,
    regenerated_document,
):
    signatures = _column_signatures(new_matrix, kernel_data.basis)
    target = _target_signature(old_system.rhs, kernel_data.basis)
    signature_system = _signature_system(
        new_matrix.parameter_names, signatures, target
    )
    certificate = regenerated_document["minimal_signature_certificate"]
    columns = tuple(record["column"] for record in certificate["columns"])
    coefficients = {
        record["column"]: _parse_fraction(record["coefficient"])
        for record in certificate["columns"]
    }

    assert columns == (0, 1, 2, 3, 4)
    assert len(coefficients) == 5
    assert all(coefficients.values())
    reproduced = tuple(
        sum(
            (
                coefficient * signatures[column][coordinate]
                for column, coefficient in coefficients.items()
            ),
            Fraction(0),
        )
        for coordinate in range(9)
    )
    assert reproduced == target
    assert certificate["target_signature_reproduced"] is True
    assert all(
        _parse_fraction(value) == 0
        for value in certificate["corrected_target_signature"]
    )

    selected = _restricted_columns(signature_system, columns)
    assert system_ranks(selected) == (5, 5)
    for removed in columns:
        reduced = _restricted_columns(
            signature_system,
            tuple(column for column in columns if column != removed),
        )
        assert system_ranks(reduced) == (4, 5)
    assert certificate["support_minimization"] == {
        "method": "exact reverse deletion from the canonical free-zero quotient solution",
        "support_size": 5,
        "inclusion_minimal": True,
        "minimum_cardinality_certified": False,
        "deletion_checks": [
            {"column": column, "status": "inconsistent"} for column in columns
        ],
    }

    combination = tuple(
        sum(
            (
                new_matrix.rows[row].get(column, Fraction(0)) * coefficient
                for column, coefficient in coefficients.items()
            ),
            Fraction(0),
        )
        for row in range(144)
    )
    residual = tuple(
        old_system.rhs[row] - combination[row] for row in range(144)
    )
    assert _target_signature(residual, kernel_data.basis) == (Fraction(0),) * 9
    residual_system = DecisionSystem(
        dimensions=(11,),
        parameter_names=old_system.parameter_names,
        row_labels=old_system.row_labels,
        rows=old_system.rows,
        rhs=residual,
        n_edges=old_system.n_edges,
    )
    assert system_ranks(residual_system) == (135, 135)
    assert certificate["corrected_target_old_matrix_ranks"] == {
        "coefficient_rank": 135,
        "augmented_rank": 135,
    }


def test_enlarged_rank_is_140_with_nullity_384_without_a_full_solve(
    old_system,
    new_matrix,
    regenerated_document,
):
    assert system_ranks(old_system)[0] == 135
    assert regenerated_document["cokernel_signatures"]["new_signature_rank"] == 5
    assert 135 + 5 == 140
    assert regenerated_document["enlarged_d11"] == {
        "parameter_count": 524,
        "coefficient_rank": 140,
        "augmented_rank": 140,
        "nullity": 384,
        "rank_derivation": (
            "rank(A4) + rank of exact new-column cokernel signatures; "
            "no 144x524 elimination constructed"
        ),
    }
    assert regenerated_document["decision_branch"] == "B_signature_spanned"
    assert regenerated_document["scope"]["full_degree5_coefficient_solve_run"] is False
    assert "full_coefficient_vector" not in regenerated_document
    assert "particular_solution" not in regenerated_document


def test_regeneration_is_deterministic_d11_only_and_exact_no_float(
    regenerated_document,
):
    repository = Path(__file__).resolve().parents[1]
    artifact = json.loads(
        repository.joinpath(
            "results", "k4_degree5_quotient_gate", "decision.json"
        ).read_text(encoding="utf-8")
    )
    assert artifact == regenerated_document
    assert artifact["schema"] == "chow-cone/k4-degree5-cokernel-gate/v1"
    assert artifact["checkpoint_base"] == (
        "0b3603807fac8698e412053204e252cfe7da2c1c"
    )
    assert artifact["scope"] == {
        "dimension": 11,
        "old_maximum_weighted_degree": 4,
        "new_exact_weighted_degree": 5,
        "full_degree5_coefficient_solve_run": False,
        "nonnegativity_optimization_run": False,
        "manual_features_added": [],
        "other_dimensions_constructed": False,
    }
    assert artifact["stopping_rule"] == (
        "stop after the exact d=11 quotient certificate; do not compute a "
        "full coefficient vector or evaluate any other dimension"
    )

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
