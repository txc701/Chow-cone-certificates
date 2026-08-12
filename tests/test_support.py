"""Validation of the support reduction (support.py) against the full map."""

import pytest

import support
import weights_bitmask as impl1
from weights_recursive import mask_of_composition


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


@pytest.mark.parametrize("d", range(1, 12))
def test_support_matches_full_map(d):
    full = impl1.weight_map(d)
    sw = support.support_weights(d)
    by_mask = {mask_of_composition(c): v for c, v in sw.items()}
    # every nonzero weight of the full map lives on an all-parts>=2 composition
    for mask, (u, a, w) in full.items():
        if w != 0:
            assert mask in by_mask, (d, mask)
        if mask in by_mask:
            assert by_mask[mask] == (u, a, w)
    # count = compositions of d+2 into parts >= 2 = Fib(d+1)  (F(1)=F(2)=1)
    assert len(sw) == fib(d + 1)


@pytest.mark.parametrize("d", range(2, 10))
def test_split_dag_reachability_equals_containment(d):
    """In the reduced DAG, K is reachable from J iff J <= K (as subsets),
    for J, K in the support.  This is the connectivity fact behind the
    reduction proof."""
    comps = support.support_compositions(d)
    children = {c: [ch for (_, _, ch) in support.split_edges(c)] for c in comps}
    # reachability by DFS from each node (support is small for d<10)
    reach = {}
    for c in comps:
        seen = {c}
        stack = [c]
        while stack:
            x = stack.pop()
            for ch in children[x]:
                if ch not in seen:
                    seen.add(ch)
                    stack.append(ch)
        reach[c] = seen
    masks = {c: mask_of_composition(c) for c in comps}
    for cj in comps:
        for ck in comps:
            contained = masks[cj] & masks[ck] == masks[cj]
            assert (ck in reach[cj]) == contained, (d, cj, ck)
