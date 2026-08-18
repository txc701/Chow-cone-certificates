"""EXPLICIT uniform peel2 certificate for Conjecture 3.30 (audited).

Independent of the max-flow machinery: flows are assigned by a closed
formula, never solved for.

For a support composition c = (n_1,...,n_r) (n_i >= 2, sum = d+2) define

    G(c) = U_c * prod_i (n_i - 1),
    U_c  = n_r * (d+1)! / prod_i n_i!,
    rho(n) = n * (n-3) // 2,

so that w(c) = G(c) * sum_i rho(n_i)  (definitional, from the pinned paper).

Flow rule (the candidate certificate):
  * every NONFINAL block n_i >= 4: single edge  n_i -> (2, n_i-2),
    flow G(child);
  * the FINAL block n_r >= 4: two edges  n_r -> (2, n_r-2)  and
    n_r -> (n_r-2, 2), each with flow G(child).  For n_r = 4 both peels are
    the same Boolean cover edge; contributions accumulate (flow 2*G(child)).

Edges are keyed (c, i, p): block i of c splits into (p, c[i]-p), matching
the (comp, i, p) vocabulary used everywhere else in this repo.
"""

from math import factorial


def g_value(c: tuple[int, ...], d: int) -> int:
    """G(c) = U_c * prod (n_i - 1), exact integer."""
    assert sum(c) == d + 2 and all(p >= 2 for p in c)
    num = c[-1] * factorial(d + 1)
    den = 1
    prod = 1
    for p in c:
        den *= factorial(p)
        prod *= p - 1
    assert num % den == 0
    return (num // den) * prod


def rho(n: int) -> int:
    assert (n * (n - 3)) % 2 == 0
    return n * (n - 3) // 2


def w_value(c: tuple[int, ...], d: int) -> int:
    """w(c) = G(c) * sum rho(n_i) — re-derived from the pinned definitions."""
    return g_value(c, d) * sum(rho(p) for p in c)


def explicit_edges(c: tuple[int, ...], d: int):
    """Yield (i, p, child, flow) for the selected out-edges of c."""
    r = len(c)
    for i, m in enumerate(c):
        if m < 4:
            continue
        if i < r - 1:
            child = c[:i] + (2, m - 2) + c[i + 1 :]
            yield i, 2, child, g_value(child, d)
        else:
            child_l = c[:i] + (2, m - 2)
            yield i, 2, child_l, g_value(child_l, d)
            child_r = c[:i] + (m - 2, 2)
            yield i, m - 2, child_r, g_value(child_r, d)


def certificate(d: int) -> dict[tuple, int]:
    """Full certificate {(c, i, p): flow} for dimension d, generated purely
    from the closed formula (accumulating coincident final-4 peels)."""
    from support import support_compositions  # enumerator only, no flow code

    flows: dict[tuple, int] = {}
    for c in support_compositions(d):
        for i, p, child, f in explicit_edges(c, d):
            key = (c, i, p)
            flows[key] = flows.get(key, 0) + f
    return flows


def divergence(d: int) -> dict[tuple[int, ...], int]:
    """out - in at every support node, computed from the explicit edges."""
    from support import support_compositions

    div: dict[tuple[int, ...], int] = {
        c: 0 for c in support_compositions(d)
    }
    for c in list(div):
        for i, p, child, f in explicit_edges(c, d):
            div[c] += f
            div[child] -= f
    return div
