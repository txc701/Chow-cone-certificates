"""Support of the weight function w, and the reduced flow DAG.

Key fact (proved in RESEARCH_NOTES.md, "Support reduction"): w_J = 0 unless
every part of the composition of J is >= 2, because a_J contains the factor
prod (n_i - 1).  Compositions of d+2 with all parts >= 2 are in bijection
with the subsets J that can carry nonzero weight; there are Fib-many of them
(6765 at d=19), so the flow problem never needs the full 2^d lattice.

The reduced DAG has these compositions as nodes and, as edges, the Boolean
cover moves J -> J u {j} that stay inside the all-parts->=2 world:
split a part n_i (>= 4) into (p, n_i - p) with 2 <= p <= n_i - 2.
RESEARCH_NOTES.md proves max-flow feasibility on the reduced DAG is
equivalent to feasibility on the full Boolean lattice.
"""

from weights_bitmask import uaw_from_composition


def support_compositions(d: int) -> list[tuple[int, ...]]:
    """All compositions of d+2 with every part >= 2, in lexicographic order."""
    n = d + 2
    out: list[tuple[int, ...]] = []

    def rec(remaining: int, parts: tuple[int, ...]) -> None:
        if remaining == 0:
            out.append(parts)
            return
        for p in range(2, remaining + 1):
            if remaining - p != 1:  # can't leave a forced part of size 1
                rec(remaining - p, parts + (p,))

    rec(n, ())
    return out


def split_edges(parts: tuple[int, ...]):
    """Yield (i, p, child) for each admissible split of parts:
    part index i with n_i >= 4 splits into (p, n_i - p), 2 <= p <= n_i - 2.
    `child` is the resulting composition (one Boolean cover step above)."""
    for i, ni in enumerate(parts):
        if ni >= 4:
            for p in range(2, ni - 1):
                yield i, p, parts[:i] + (p, ni - p) + parts[i + 1 :]


def support_weights(d: int) -> dict[tuple[int, ...], tuple[int, int, int]]:
    """Map composition -> (U, a, w) over the all-parts->=2 compositions."""
    return {c: uaw_from_composition(c, d) for c in support_compositions(d)}
