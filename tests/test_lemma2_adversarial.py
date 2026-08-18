"""Adversarial re-audit of PROOF_CONJECTURE_3_30.md Lemma 2 (in-edges).

Checks the lemma's EXACT constructive description — not just the counts it
implies: for every support composition c, the multiset of selected moves
with child c (obtained by exhaustive forward enumeration over ALL parents)
equals the lemma's predicted multiset of (parent, block index, offset)
triples; every in-flow equals G(c); the in-edge count equals the number of
2-blocks; the FL/FR edge coincidence happens exactly when c ends (2,2);
and the added-element claims (j = prefix+2 for N/FL, j = d for FR) plus the
parity property used by Corollary 1 hold on every selected edge.
"""

from collections import defaultdict

import pytest

from explicit_certificate import explicit_edges, g_value
from support import support_compositions
from weights_recursive import mask_of_composition


@pytest.mark.parametrize("d", range(2, 12))
def test_lemma2_exact_parent_multiset(d):
    comps = support_compositions(d)
    in_edges = defaultdict(list)
    for p_comp in comps:
        for i, p, child, f in explicit_edges(p_comp, d):
            in_edges[child].append((p_comp, i, p, f))
    for c in comps:
        r = len(c)
        got = in_edges[c]
        expected = []
        for idx in range(r):  # 0-based
            if c[idx] != 2:
                continue
            if idx <= r - 3:
                expected.append((c[:idx] + (2 + c[idx + 1],) + c[idx + 2 :], idx, 2))
            elif idx == r - 2:
                expected.append((c[:idx] + (2 + c[idx + 1],), idx, 2))
            else:
                expected.append((c[: r - 2] + (c[r - 2] + 2,), r - 2, c[r - 2]))
        assert sorted((pp, i, p) for (pp, i, p, _) in got) == sorted(expected), c
        assert all(f == g_value(c, d) for (_, _, _, f) in got), c
        assert len(got) == sum(1 for x in c if x == 2), c
        keyset = {(pp, i, p) for (pp, i, p, _) in got}
        assert (len(keyset) < len(got)) == (
            r >= 2 and c[-1] == 2 and c[-2] == 2
        ), c


@pytest.mark.parametrize("d", range(2, 12))
def test_cut_point_claims(d):
    for p_comp in support_compositions(d):
        mask = mask_of_composition(p_comp)
        for i, p, child, f in explicit_edges(p_comp, d):
            j = sum(p_comp[:i]) + p
            assert (p == 2) or j == d, (p_comp, i, p)
            if j % 2 == 1 and j < d:
                assert any((mask >> (e - 1)) & 1 for e in range(1, j, 2)), (
                    p_comp,
                    j,
                )
