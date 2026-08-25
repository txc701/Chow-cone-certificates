"""Exact d=4 audit of reversal symmetry and the proposed phi_G column."""

from fractions import Fraction

from k4_certificates import allowed_edge_keys
from k4_feature_analysis import g_value
from k4_weights import s4, support_w4
from support import support_compositions


D = 4
COMPOSITIONS = tuple(sorted(support_compositions(D)))
EDGES = tuple(allowed_edge_keys(D))
WITNESS = {(2, 2, 2): -1, (2, 4): 2, (4, 2): -2}


def _reverse_composition(composition):
    return tuple(reversed(composition))


def _child(edge):
    parent, block, left = edge
    return (
        parent[:block]
        + (left, parent[block] - left)
        + parent[block + 1 :]
    )


def _reverse_edge(edge):
    parent, block, left = edge
    return (
        _reverse_composition(parent),
        len(parent) - 1 - block,
        parent[block] - left,
    )


def _alpha(composition):
    return Fraction(
        g_value(_reverse_composition(composition), D),
        g_value(composition, D),
    )


def _raw_divergence(flow):
    divergence = {composition: Fraction(0) for composition in COMPOSITIONS}
    for edge in EDGES:
        value = Fraction(flow[edge])
        divergence[edge[0]] += value
        divergence[_child(edge)] -= value
    return divergence


def _reflect_raw(flow):
    return {edge: Fraction(flow[_reverse_edge(edge)]) for edge in EDGES}


def _normalized_divergence(q):
    divergence = {composition: Fraction(0) for composition in COMPOSITIONS}
    for edge in EDGES:
        parent = edge[0]
        child = _child(edge)
        value = Fraction(q[edge])
        divergence[parent] += Fraction(
            g_value(child, D), g_value(parent, D)
        ) * value
        divergence[child] -= value
    return divergence


def _plain_reflect_normalized(q):
    return {edge: Fraction(q[_reverse_edge(edge)]) for edge in EDGES}


def _true_reflect_normalized(q):
    return {
        edge: _alpha(_child(edge)) * Fraction(q[_reverse_edge(edge)])
        for edge in EDGES
    }


def _witness_pairing(divergence):
    return sum(
        Fraction(multiplier) * divergence[composition]
        for composition, multiplier in WITNESS.items()
    )


def _phi_g(edge):
    parent, block, left = edge
    right = parent[block] - left
    if min(left, right) == 2 and left != right:
        return Fraction(_child(edge)[0])
    return Fraction(0)


def test_reversal_is_an_involution_of_the_oriented_support_dag():
    compositions = set(COMPOSITIONS)
    edges = set(EDGES)
    assert len(compositions) == 5
    assert len(edges) == 5

    for composition in compositions:
        reflected = _reverse_composition(composition)
        assert reflected in compositions
        assert _reverse_composition(reflected) == composition

    for edge in edges:
        reflected = _reverse_edge(edge)
        assert reflected in edges
        assert _reverse_edge(reflected) == edge
        assert _child(reflected) == _reverse_composition(_child(edge))
        assert len(_child(reflected)) == len(reflected[0]) + 1
        parent, block, left = edge
        reflected_parent, reflected_block, reflected_left = reflected
        assert min(left, parent[block] - left) == min(
            reflected_left,
            reflected_parent[reflected_block] - reflected_left,
        )


def test_target_has_covariance_not_reversal_invariance():
    weights = support_w4(D)
    for composition in COMPOSITIONS:
        reflected = _reverse_composition(composition)
        assert _alpha(composition) == Fraction(composition[0], composition[-1])
        assert s4(reflected) == s4(composition)
        assert weights[reflected] == _alpha(composition) * weights[composition]

    assert g_value((2, 4), D) == 30
    assert g_value((4, 2), D) == 15
    assert weights[(2, 4)] == -720
    assert weights[(4, 2)] == -360


def test_raw_reflection_preserves_support_and_nonnegativity_but_not_target():
    feasible = {
        ((2, 4), 1, 2): 0,
        ((4, 2), 0, 2): 15120,
        ((6,), 0, 2): 720,
        ((6,), 0, 3): 5760,
        ((6,), 0, 4): 15480,
    }
    weights = {composition: Fraction(value) for composition, value in support_w4(D).items()}
    assert set(feasible) == set(EDGES)
    assert all(value >= 0 for value in feasible.values())
    assert _raw_divergence(feasible) == weights

    reflected = _reflect_raw(feasible)
    assert set(reflected) == set(EDGES)
    assert all(value >= 0 for value in reflected.values())
    assert _reflect_raw(reflected) == {
        edge: Fraction(value) for edge, value in feasible.items()
    }
    assert _raw_divergence(reflected) == {
        composition: weights[_reverse_composition(composition)]
        for composition in COMPOSITIONS
    }
    assert _raw_divergence(reflected) != weights

    averaged = {
        edge: (Fraction(feasible[edge]) + reflected[edge]) * Fraction(1, 2)
        for edge in EDGES
    }
    averaged_divergence = _raw_divergence(averaged)
    assert all(value >= 0 for value in averaged.values())
    assert averaged_divergence == {
        composition: (
            weights[composition] + weights[_reverse_composition(composition)]
        )
        * Fraction(1, 2)
        for composition in COMPOSITIONS
    }
    assert averaged_divergence[(2, 4)] == -540
    assert averaged_divergence[(4, 2)] == -540
    assert averaged_divergence != weights


def test_true_normalized_reversal_has_explicit_child_factor_and_scales_rows():
    raw = {edge: Fraction(index + 1) for index, edge in enumerate(EDGES)}
    q = {
        edge: raw[edge] * Fraction(1, g_value(_child(edge), D))
        for edge in EDGES
    }
    true_reflection = _true_reflect_normalized(q)
    reflected_raw_normalized = {
        edge: _reflect_raw(raw)[edge] * Fraction(1, g_value(_child(edge), D))
        for edge in EDGES
    }
    assert true_reflection == reflected_raw_normalized
    assert _true_reflect_normalized(true_reflection) == q

    divergence = _normalized_divergence(q)
    reflected_divergence = _normalized_divergence(true_reflection)
    assert reflected_divergence == {
        composition: _alpha(composition)
        * divergence[_reverse_composition(composition)]
        for composition in COMPOSITIONS
    }

    left = ((6,), 0, 2)
    right = _reverse_edge(left)
    assert right == ((6,), 0, 4)
    assert _alpha(_child(left)) == Fraction(1, 2)
    assert _alpha(_child(right)) == 2


def test_phi_g_is_legal_and_true_covariant_on_every_d4_edge():
    phi = {edge: _phi_g(edge) for edge in EDGES}
    expected = {
        ((2, 4), 1, 2): Fraction(0),
        ((4, 2), 0, 2): Fraction(0),
        ((6,), 0, 2): Fraction(2),
        ((6,), 0, 3): Fraction(0),
        ((6,), 0, 4): Fraction(4),
    }
    assert phi == expected
    assert all(value >= 0 for value in phi.values())

    plain_partner = _plain_reflect_normalized(phi)
    assert plain_partner == {
        ((2, 4), 1, 2): Fraction(0),
        ((4, 2), 0, 2): Fraction(0),
        ((6,), 0, 2): Fraction(4),
        ((6,), 0, 3): Fraction(0),
        ((6,), 0, 4): Fraction(2),
    }
    assert plain_partner != phi
    assert phi[((6,), 0, 2)] * plain_partner[((6,), 0, 4)] != (
        phi[((6,), 0, 4)] * plain_partner[((6,), 0, 2)]
    )

    symmetric = {
        edge: (phi[edge] + plain_partner[edge]) * Fraction(1, 2)
        for edge in EDGES
    }
    antisymmetric = {
        edge: (phi[edge] - plain_partner[edge]) * Fraction(1, 2)
        for edge in EDGES
    }
    assert _plain_reflect_normalized(symmetric) == symmetric
    assert _plain_reflect_normalized(antisymmetric) == {
        edge: -value for edge, value in antisymmetric.items()
    }

    assert _true_reflect_normalized(phi) == phi
    raw_column = {
        edge: g_value(_child(edge), D) * value for edge, value in phi.items()
    }
    assert raw_column == {
        ((2, 4), 1, 2): Fraction(0),
        ((4, 2), 0, 2): Fraction(0),
        ((6,), 0, 2): Fraction(60),
        ((6,), 0, 3): Fraction(0),
        ((6,), 0, 4): Fraction(60),
    }
    assert _reflect_raw(raw_column) == raw_column


def test_phi_g_full_divergence_and_witness_pairing_force_positive_126():
    phi = {edge: _phi_g(edge) for edge in EDGES}
    plain_partner = _plain_reflect_normalized(phi)
    symmetric = {
        edge: (phi[edge] + plain_partner[edge]) * Fraction(1, 2)
        for edge in EDGES
    }
    antisymmetric = {
        edge: (phi[edge] - plain_partner[edge]) * Fraction(1, 2)
        for edge in EDGES
    }

    divergence = _normalized_divergence(phi)
    assert divergence == {
        (2, 2, 2): Fraction(0),
        (2, 4): Fraction(-2),
        (3, 3): Fraction(0),
        (4, 2): Fraction(-4),
        (6,): Fraction(24),
    }
    assert _witness_pairing(divergence) == 4
    assert _witness_pairing(_normalized_divergence(plain_partner)) == -4
    assert _witness_pairing(_normalized_divergence(symmetric)) == 0
    assert _witness_pairing(_normalized_divergence(antisymmetric)) == 4
    assert Fraction(504, _witness_pairing(divergence)) == 126
