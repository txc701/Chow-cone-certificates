"""Exact tests for the bounded cumulative desymmetrized equality scan."""

from fractions import Fraction
from functools import reduce
import json
from math import gcd
from pathlib import Path
import tokenize

import pytest

from k4_degree4_decision import DecisionSystem, evaluate_sparse_row, verify_solution
from k4_desymmetrized_d4 import lifted_normalized_flow_row
from k4_desymmetrized_scan import (
    MAXIMUM_DIMENSION,
    MINIMUM_DIMENSION,
    build_cumulative_system,
    build_dimension_system,
    d4_conservation_relation,
    deduplicate_system,
    run_progressive_scan,
    system_hashes,
)
from k4_feature_analysis import edge_features
from k4_weights import s4
from support import support_compositions


DIMENSIONS = tuple(range(4, 11))
DIMENSION_RAW_COUNTS = (5, 8, 13, 21, 34, 55, 89)
CUMULATIVE_RAW_COUNTS = (5, 13, 26, 47, 81, 136, 225)
RANK_SEQUENCE = (4, 11, 23, 43, 76, 130, 217)
RANK_INCREMENTS = (4, 7, 12, 20, 33, 54, 87)
NULLITY_SEQUENCE = (272, 265, 253, 233, 200, 146, 59)
MATRIX_HASHES = (
    "6a3fa99832757d90d4cd7d0e8e2cf75dc0156a984d93418159601db6899581ab",
    "a26e8bcb19bd7e13e433cceaa55acf9b27aeb147abe4e40331e98552dac9fc13",
    "cfd0f9f1e2a41bc7eedfd9c555fe0882b87549de37115215752a562604e42489",
    "10e7d604c3ad957b1bec0967bf7ce5566bd10b964af5d05a8df7ea1ddf27bf97",
    "a0c4ba1338e9f167219ba31357b6c0ccc2debcc1fdf94a1fa21613d981c154b4",
    "26e3b5006e569954d7904ba830638e7ad45fcc9da52daddbe8cf35cade3cadb3",
    "3ab29b5c8c4db6251272db846b18748bd4fb2757276e8261ebbab9e0de2c94af",
)
RHS_HASHES = (
    "355b054e8f5fbf7bf0fcc364fa4169cfb4f988687915ba49dce5e8c7501966df",
    "1e657e0217d971c1a374515b4c21a84980fb40bd2d9efdb8e18cd665250d6fa4",
    "1e185d73ca48ef2db1889490a80a0489912c7fba6b26989399ca70a7e2a2fb18",
    "5e7d5ef4b6911ed32e0a0bb599755168d087df7149f453a2334ffcbdc69fea7d",
    "480837bd03467ef426b8e58e127e899072797451be44511542b911f3cd360164",
    "584ccbd154a012c98888a497d8e1813a9c50ab6d767838234d441a94a0004fe8",
    "b884de88fcdc4aa29a5ea8b0330d770c295cfeb5d6980f3cd650fc6f0bc0e1a8",
)
SYSTEM_HASHES = (
    "6cc09dd1e57d0bc8161195a373d2b9a60d40bb0da12471744e3923a73ffbd0d4",
    "720caee22023f8dff651fe605b83033a5f26d59ad76f35cba903bf009ce05bbd",
    "d59b4732c9677eca37fab558f1157536ca9b9510a5242fb7fd48b447629f3604",
    "66c3ed9ec8cba537840787f70286e7f2e2021b7ce2f1ab9501ea77728f474ed6",
    "2e967c60d2eefb61f01ec721848e0f7722c1f1dbb9cddf4111f77ef35480ffae",
    "2493a694891411aa775b438d548a5158c1fb34a16c8c9bc1387432695754442f",
    "74440aade255dd61367e0671bffdb490cbe9fb4a1af5b7f6e86f2a6de5d58a53",
)


@pytest.fixture(scope="module")
def cumulative_system():
    return build_cumulative_system(MAXIMUM_DIMENSION)


@pytest.fixture(scope="module")
def deduplicated_system(cumulative_system):
    return deduplicate_system(cumulative_system)


@pytest.fixture(scope="module")
def scan_document():
    return run_progressive_scan()


def _parse_fraction(record):
    return Fraction(int(record["num"]), int(record["den"]))


def _solution_vector(document, n_parameters):
    coefficients = [Fraction(0) for _ in range(n_parameters)]
    for record in document["solution"]["nonzero_coefficients"]:
        column = record["column"]
        assert 0 <= column < n_parameters
        assert coefficients[column] == 0
        coefficients[column] = _parse_fraction(record["value"])
    return tuple(coefficients)


def test_d4_primitive_left_null_relation_is_exact_conservation():
    system = build_dimension_system(4)
    relation = d4_conservation_relation()
    multipliers = tuple(
        int(value) for value in relation["primitive_integer_vector"]
    )

    assert relation["G_values"] == ["30", "30", "40", "15", "5"]
    assert relation["G_common_divisor"] == "5"
    assert multipliers == (6, 6, 8, 3, 1)
    assert reduce(gcd, multipliers) == 1
    assert relation["coefficient_rank"] == 4
    assert relation["left_nullity"] == 1

    column_sums = {}
    for multiplier, row in zip(multipliers, system.rows):
        for column, value in row.items():
            updated = column_sums.get(column, Fraction(0)) + multiplier * value
            if updated:
                column_sums[column] = updated
            elif column in column_sums:
                del column_sums[column]
    assert column_sums == {}
    assert sum(
        (multiplier * rhs for multiplier, rhs in zip(multipliers, system.rhs)),
        Fraction(0),
    ) == 0
    assert relation["verification"] == {
        "nonzero_column_sums": 0,
        "target_dot": {"num": "0", "den": "1"},
    }


def test_cumulative_system_uses_one_shared_276_parameter_vector(cumulative_system):
    assert cumulative_system.dimensions == DIMENSIONS
    assert len(cumulative_system.parameter_names) == 276
    assert len(set(cumulative_system.parameter_names)) == 276
    assert len(cumulative_system.rows) == 225
    assert len(cumulative_system.rhs) == 225
    assert all(
        not row or max(row) < 276
        for row in cumulative_system.rows
    )
    assert tuple(
        sum(label[0] == dimension for label in cumulative_system.row_labels)
        for dimension in DIMENSIONS
    ) == DIMENSION_RAW_COUNTS


def test_raw_deduplicated_counts_and_exact_rank_sequence_through_d10(
    cumulative_system,
    deduplicated_system,
    scan_document,
):
    prefixes = scan_document["prefixes"]
    assert tuple(prefix["maximum_dimension"] for prefix in prefixes) == DIMENSIONS
    assert tuple(prefix["dimension_raw_equations"] for prefix in prefixes) == (
        DIMENSION_RAW_COUNTS
    )
    assert tuple(prefix["cumulative_raw_equations"] for prefix in prefixes) == (
        CUMULATIVE_RAW_COUNTS
    )
    assert tuple(
        prefix["cumulative_deduplicated_equations"] for prefix in prefixes
    ) == CUMULATIVE_RAW_COUNTS
    assert tuple(prefix["coefficient_rank"] for prefix in prefixes) == RANK_SEQUENCE
    assert tuple(prefix["augmented_rank"] for prefix in prefixes) == RANK_SEQUENCE
    assert tuple(
        prefix["new_independent_constraints_from_dimension"]
        for prefix in prefixes
    ) == RANK_INCREMENTS
    assert tuple(prefix["nullity"] for prefix in prefixes) == NULLITY_SEQUENCE

    assert len(deduplicated_system.system.rows) == len(cumulative_system.rows) == 225
    assert deduplicated_system.retained_raw_rows == tuple(range(225))
    assert deduplicated_system.raw_to_deduplicated == tuple(range(225))


def test_augmented_row_deduplication_handles_exact_scaling_and_zero_rows():
    synthetic = DecisionSystem(
        dimensions=(4,),
        parameter_names=("x",),
        row_labels=tuple((4, (index + 2,)) for index in range(6)),
        rows=(
            {0: Fraction(1)},
            {0: Fraction(2)},
            {0: Fraction(-1, 2)},
            {0: Fraction(1)},
            {},
            {},
        ),
        rhs=(
            Fraction(2),
            Fraction(4),
            Fraction(-1),
            Fraction(3),
            Fraction(0),
            Fraction(7),
        ),
        n_edges=0,
    )
    result = deduplicate_system(synthetic)
    assert result.retained_raw_rows == (0, 3, 4, 5)
    assert result.raw_to_deduplicated == (0, 0, 0, 1, 2, 3)
    assert len(result.system.rows) == 4


def test_consistent_exact_solution_has_zero_residual_and_d10_shrinks_space(
    deduplicated_system,
    scan_document,
):
    system = deduplicated_system.system
    coefficients = _solution_vector(scan_document, len(system.parameter_names))
    verification = verify_solution(system, coefficients)

    assert scan_document["decision"] == "consistent_through_d10"
    assert scan_document["first_inconsistent_dimension"] is None
    assert verification == {
        "verified": True,
        "n_rows": 225,
        "n_parameters": 276,
        "n_mismatches": 0,
        "first_mismatch": None,
    }
    assert scan_document["solution"]["verification"] == verification
    assert scan_document["d10_effect"] == {
        "new_independent_constraints": 87,
        "interpretation": "d=10 rows shrink the preceding affine solution space",
    }
    assert scan_document["prefixes"][-2]["nullity"] == 146
    assert scan_document["prefixes"][-1]["nullity"] == 59
    assert scan_document["affine_solution_space_dimension"] == 59
    assert scan_document["solution"]["per_dimension_residuals"] == [
        {"d": d, "n_rows": n_rows, "n_nonzero_residuals": 0}
        for d, n_rows in zip(DIMENSIONS, DIMENSION_RAW_COUNTS)
    ]

    for d in DIMENSIONS:
        divergence = {
            composition: Fraction(0) for composition in support_compositions(d)
        }
        for feature in edge_features(d):
            flow = evaluate_sparse_row(
                lifted_normalized_flow_row(feature), coefficients
            )
            divergence[feature.parent] += feature.ratio * flow
            divergence[feature.child] -= flow
        assert divergence == {
            composition: Fraction(s4(composition))
            for composition in support_compositions(d)
        }


def test_deterministic_hashes_and_saved_artifact_document(
    cumulative_system,
    scan_document,
):
    prefixes = scan_document["prefixes"]
    assert tuple(
        prefix["raw_hashes"]["matrix_sha256"] for prefix in prefixes
    ) == MATRIX_HASHES
    assert tuple(
        prefix["raw_hashes"]["rhs_sha256"] for prefix in prefixes
    ) == RHS_HASHES
    assert tuple(
        prefix["raw_hashes"]["system_sha256"] for prefix in prefixes
    ) == SYSTEM_HASHES
    assert all(
        prefix["raw_hashes"] == prefix["deduplicated_hashes"]
        for prefix in prefixes
    )
    assert system_hashes(cumulative_system) == {
        "matrix_sha256": MATRIX_HASHES[-1],
        "rhs_sha256": RHS_HASHES[-1],
        "system_sha256": SYSTEM_HASHES[-1],
    }

    repository = Path(__file__).resolve().parents[1]
    artifact = json.loads(
        repository.joinpath(
            "results", "k4_desymmetrized_scan", "decision.json"
        ).read_text(encoding="utf-8")
    )
    assert artifact == scan_document
    assert artifact["scope"] == {
        "minimum_dimension": 4,
        "maximum_authorized_dimension": 10,
        "largest_dimension_constructed": 10,
        "shared_parameter_count": 276,
        "single_shared_coefficient_vector": True,
        "nonnegativity_optimization_run": False,
        "manual_features_appended": [],
        "dimensions_above_10_constructed": False,
    }


def test_scan_source_has_no_floating_point_or_true_division():
    source = Path(__file__).resolve().parents[1].joinpath(
        "src", "k4_desymmetrized_scan.py"
    )
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


def test_dimension_api_is_hard_bounded_to_integer_prefixes():
    for invalid in (3, 11, True, False, 4.0, "4", None):
        with pytest.raises(ValueError):
            build_dimension_system(invalid)
        with pytest.raises(ValueError):
            build_cumulative_system(invalid)
    assert MINIMUM_DIMENSION == 4
    assert MAXIMUM_DIMENSION == 10
