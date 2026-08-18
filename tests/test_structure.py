"""Stage 3 structural discoveries, pinned as regression tests.

1. Staircase characterization: the tight principal ideals sigma(T) :=
   sum_{J <= T} w_J = 0 are exactly {T_k, T_k u {1}} for
   T_k = {2,4,...,2k} u {2k+1,...,d}, 0 <= k <= d//2; and sigma(T) >= 0
   for ALL T (principal-ideal nonnegativity).
2. Shell identities: grouping support compositions by their smallest odd
   proper prefix sum (residual class for >= 2*(d//2)+1 or none), every
   group's weight sum vanishes.
3. Shell decomposition: freshly extracted max-flow certificates never carry
   flow between different shells (forced by 1+2; checked directly).
"""

import pytest

from certificates import HEURISTICS, extract_certificate
from support import support_weights
from weights_bitmask import weight_map


def staircase_masks(d):
    fam = set()
    for k in range(d // 2 + 1):
        mask = 0
        for e in range(2, 2 * k + 1, 2):
            mask |= 1 << (e - 1)
        for e in range(2 * k + 1, d + 1):
            mask |= 1 << (e - 1)
        fam.add(mask)
        fam.add(mask | 1)
    return fam


def shell_of(c, d):
    j = 0
    for p in c[:-1]:
        j += p
        if j % 2 == 1:
            return j if j <= 2 * (d // 2) - 1 else "residual"
    return "residual"


@pytest.mark.parametrize("d", range(2, 11))
def test_staircase_characterization(d):
    wm = weight_map(d)
    f = [wm[m][2] for m in range(1 << d)]
    for b in range(d):
        bit = 1 << b
        for m in range(1 << d):
            if m & bit:
                f[m] += f[m ^ bit]
    assert min(f) == 0  # no principal ideal is negative; 0 attained
    assert {m for m in range(1 << d) if f[m] == 0} == staircase_masks(d)


@pytest.mark.parametrize("d", range(2, 15))
def test_shell_sums_vanish(d):
    sums = {}
    for c, (_, _, w) in support_weights(d).items():
        key = shell_of(c, d)
        sums[key] = sums.get(key, 0) + w
    assert all(v == 0 for v in sums.values()), (d, sums)


@pytest.mark.parametrize("d", range(4, 10))
def test_certificates_respect_shells(d):
    for h in HEURISTICS:
        _, flow_edges = extract_certificate(d, h)
        for c, i, p, f in flow_edges:
            child = c[:i] + (p, c[i] - p) + c[i + 1 :]
            assert shell_of(c, d) == shell_of(child, d), (d, h, c, child)
