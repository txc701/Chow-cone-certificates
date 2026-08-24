"""Exact generation, standalone verification, and nonuniqueness tests."""

from copy import deepcopy

import pytest

from k4_certificates import (
    COST_PROFILES,
    EDGE_ORDERS,
    allowed_edge_keys,
    certificate_objective_value,
    certificate_document,
    edgewise_ranges,
    min_cost_certificate_document,
    solve_certificate,
    solve_min_cost_certificate,
)
from k4_weights import support_w4
from verify_k4_certificates import (
    CertificateVerificationError,
    support_compositions_independent,
    verify_certificate,
    w4_independent,
)


EXPECTED_GRAPH_SIZES = {
    2: (2, 1),
    3: (3, 2),
    4: (5, 5),
    5: (8, 10),
    6: (13, 19),
    7: (21, 36),
    8: (34, 66),
    9: (55, 120),
    10: (89, 215),
}


@pytest.mark.parametrize("d", range(2, 11))
def test_independent_weights_and_graph_match_existing_definition(d):
    independent_compositions = support_compositions_independent(d)
    canonical = support_w4(d)
    assert independent_compositions == sorted(canonical)
    assert {
        composition: w4_independent(composition, d)
        for composition in independent_compositions
    } == canonical
    expected_nodes, expected_edges = EXPECTED_GRAPH_SIZES[d]
    assert len(independent_compositions) == expected_nodes
    assert len(allowed_edge_keys(d)) == expected_edges


@pytest.mark.parametrize("d", range(2, 9))
def test_generated_certificate_passes_standalone_verifier(d):
    document = certificate_document(d)
    summary = verify_certificate(document)
    assert summary["verified"]
    assert summary["d"] == d
    assert summary["divergence_mismatches"] == 0
    assert summary["total_weight"] == "0"
    assert summary["total_divergence"] == "0"


@pytest.mark.parametrize("edge_order", sorted(EDGE_ORDERS))
def test_named_edge_orders_are_deterministic_and_exact(edge_order):
    first = certificate_document(7, edge_order=edge_order)
    second = certificate_document(7, edge_order=edge_order)
    assert first == second
    assert first["generation"]["edge_order"] == edge_order
    assert verify_certificate(first)["verified"]


def test_exact_edge_ranges_contain_all_sampled_certificates():
    d = 8
    base = solve_certificate(d, edge_order="lex")
    ranges = edgewise_ranges(d, base)
    assert set(ranges) == set(allowed_edge_keys(d))
    assert all(
        item.minimum <= item.current <= item.maximum
        for item in ranges.values()
    )
    assert all(
        item.classification
        in {"fixed_zero", "fixed_positive", "optional", "forced_variable"}
        for item in ranges.values()
    )
    for strategy in EDGE_ORDERS:
        sampled = solve_certificate(d, edge_order=strategy)
        for edge, item in ranges.items():
            assert item.minimum <= sampled.get(edge, 0) <= item.maximum

    # Endpoints and classifications are properties of the feasible polytope,
    # not of the arbitrary certificate used to construct its residual graph.
    reverse_ranges = edgewise_ranges(
        d, solve_certificate(d, edge_order="reverse_lex")
    )
    for edge, item in ranges.items():
        reverse = reverse_ranges[edge]
        assert (item.minimum, item.maximum, item.classification) == (
            reverse.minimum,
            reverse.maximum,
            reverse.classification,
        )


def _flow_from_document(document):
    return {
        (tuple(parent), block, left): int(flow)
        for parent, block, left, flow in document["edges"]
    }


@pytest.mark.parametrize("d", range(2, 9))
@pytest.mark.parametrize("objective", sorted(COST_PROFILES))
def test_min_cost_objectives_are_exact_and_schema_compatible(d, objective):
    document = min_cost_certificate_document(d, objective)
    summary = verify_certificate(document)
    assert summary["verified"]
    assert document["generation"]["edge_order"] == "lex"
    assert document["objective"]["name"] == objective

    sparse = _flow_from_document(document)
    direct = 0
    profile = COST_PROFILES[objective]
    for (parent, block, left), flow in sparse.items():
        child = (
            parent[:block]
            + (left, parent[block] - left)
            + parent[block + 1 :]
        )
        unit_cost = profile(d, parent, block, left, child)
        assert isinstance(unit_cost, int) and unit_cost >= 0
        direct += unit_cost * flow

    recorded = int(document["objective"]["value"])
    assert recorded == direct
    assert recorded == certificate_objective_value(d, sparse, objective)

    # A genuine secondary optimum cannot cost more than an arbitrary exact
    # feasible certificate evaluated under the same objective.
    arbitrary = solve_certificate(d, edge_order="reverse_lex")
    assert recorded <= certificate_objective_value(d, arbitrary, objective)


@pytest.mark.parametrize("objective", sorted(COST_PROFILES))
def test_min_cost_solver_and_document_are_deterministic(objective):
    first_flow, first_cost = solve_min_cost_certificate(8, objective)
    second_flow, second_cost = solve_min_cost_certificate(8, objective)
    assert (first_flow, first_cost) == (second_flow, second_cost)
    document = min_cost_certificate_document(8, objective)
    assert _flow_from_document(document) == first_flow
    assert int(document["objective"]["value"]) == first_cost


def _valid_document_for_corruption_tests():
    document = certificate_document(8)
    assert document["edges"]
    return document


def test_verifier_rejects_negative_sparse_flow():
    document = _valid_document_for_corruption_tests()
    document["edges"][0][3] = "-1"
    with pytest.raises(CertificateVerificationError, match="must be positive"):
        verify_certificate(document)


def test_verifier_rejects_duplicate_edge():
    document = _valid_document_for_corruption_tests()
    document["edges"].append(deepcopy(document["edges"][0]))
    document["n_positive_edges"] += 1
    with pytest.raises(CertificateVerificationError, match="duplicate edge|canonical"):
        verify_certificate(document)


def test_verifier_rejects_width_four_edge():
    document = _valid_document_for_corruption_tests()
    document["edges"].append([[10], 0, 4, "1"])
    document["edges"].sort(key=lambda row: (tuple(row[0]), row[1], row[2]))
    document["n_positive_edges"] += 1
    with pytest.raises(CertificateVerificationError, match="width greater than 3"):
        verify_certificate(document)


def test_verifier_rejects_exact_divergence_corruption():
    document = _valid_document_for_corruption_tests()
    old = int(document["edges"][0][3])
    document["edges"][0][3] = str(old + 1)
    with pytest.raises(CertificateVerificationError, match="divergence mismatch"):
        verify_certificate(document)
