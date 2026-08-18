"""The explicit uniform peel2 certificate (src/explicit_certificate.py).

These tests pin the PROOF of Conjecture 3.30 (PROOF_CONJECTURE_3_30.md):
an explicit nonnegative flow on Boolean cover edges whose divergence equals
w_J at every node, for every d, given by f = G(child) per selected peel move.
"""

import pytest

from explicit_certificate import (
    certificate,
    divergence,
    explicit_edges,
    g_value,
    rho,
)
from support import support_compositions
from weights_bitmask import uaw_from_composition, weight_map
from weights_recursive import mask_of_composition


@pytest.mark.parametrize("d", range(1, 13))
def test_divergence_equals_w_on_support(d):
    div = divergence(d)
    for c, val in div.items():
        assert val == uaw_from_composition(c, d)[2], (d, c)


@pytest.mark.parametrize("d", range(1, 9))
def test_divergence_equals_w_full_boolean(d):
    wm = weight_map(d)
    div = {m: 0 for m in range(1 << d)}
    for c in support_compositions(d):
        mask = mask_of_composition(c)
        for i, p, child, f in explicit_edges(c, d):
            child_mask = mask_of_composition(child)
            added = child_mask & ~mask
            assert added and added & (added - 1) == 0  # exactly one element
            div[mask] += f
            div[child_mask] -= f
    for m in range(1 << d):
        assert div[m] == wm[m][2], (d, m)


@pytest.mark.parametrize("d", range(2, 13))
def test_positivity_and_peel2(d):
    for (c, i, p), f in certificate(d).items():
        assert f > 0
        assert c[i] >= 4 and (p == 2 or c[i] - p == 2)


def test_ratio_lemma_small():
    # nonfinal: G(...,2,m-2,...) = rho(m) * G(...,m,...)
    # final:    G(...,2,m-2) = (m-2)(m-3)/2 * G(...,m)
    #           G(...,m-2,2) = (m-3) * G(...,m)
    for m in range(4, 30):
        c = (3, m, 2)
        d = sum(c) - 2
        assert g_value((3, 2, m - 2, 2), d) == rho(m) * g_value(c, d)
        c2 = (3, m)
        d2 = sum(c2) - 2
        assert 2 * g_value((3, 2, m - 2), d2) == (m - 2) * (m - 3) * g_value(c2, d2)
        assert g_value((3, m - 2, 2), d2) == (m - 3) * g_value(c2, d2)


@pytest.mark.parametrize("d", range(2, 13))
def test_certificate_respects_staircase_ideals(d):
    """No selected edge leaves any staircase ideal D_k (this is the parity
    argument that proves the staircase identities for all d)."""
    for c in support_compositions(d):
        mask = mask_of_composition(c)
        for i, p, child, f in explicit_edges(c, d):
            child_mask = mask_of_composition(child)
            j = (child_mask & ~mask).bit_length()  # the added element
            if j % 2 == 1 and j < d:  # odd non-terminal cut point
                # parent must already contain an odd element below j
                assert any(
                    (mask >> (e - 1)) & 1 for e in range(1, j, 2)
                ), (d, c, child, j)
