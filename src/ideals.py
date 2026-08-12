"""Brute-force oracle for d <= 5: enumerate ALL downward-closed order ideals
of the Boolean lattice 2^[d] and minimise the weight sum over them.

Down-closed here means: J in D and J' subset of J  =>  J' in D.
(Dedekind numbers: 3, 6, 20, 168, 7581 ideals for d = 1..5, counting both
the empty ideal and the full lattice.)

Used ONLY as a small-d oracle against the max-flow decision; never run this
for d > 5.
"""

from weights_bitmask import weight_map

DEDEKIND = {1: 3, 2: 6, 3: 20, 4: 168, 5: 7581}


def enumerate_ideals(d: int):
    """Yield each down-closed ideal as a frozenset of masks."""
    assert d <= 5, "ideal enumeration is a small-d oracle only"
    masks = sorted(range(1 << d), key=lambda m: (m.bit_count(), m))
    subsets_one_less = {
        m: [m & ~(1 << b) for b in range(d) if (m >> b) & 1] for m in masks
    }

    def rec(k: int, current: set):
        if k == len(masks):
            yield frozenset(current)
            return
        m = masks[k]
        # exclude m
        yield from rec(k + 1, current)
        # include m if all immediate subsets are in (=> all subsets, inductively)
        if all(s in current for s in subsets_one_less[m]):
            current.add(m)
            yield from rec(k + 1, current)
            current.remove(m)

    yield from rec(0, set())


def min_ideal_sum(d: int):
    """(min over ideals of sum_{J in D} w_J, one attaining ideal, #ideals)."""
    wm = weight_map(d)
    best = None
    best_ideal = None
    count = 0
    for ideal in enumerate_ideals(d):
        count += 1
        s = sum(wm[m][2] for m in ideal)
        if best is None or s < best:
            best, best_ideal = s, ideal
    assert count == DEDEKIND[d], (d, count)
    return best, best_ideal, count
