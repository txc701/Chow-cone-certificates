"""Which linear functionals of the Chow distribution admit a Cheng-Lin-style
monotonicity certificate?

For a function phi on {0,...,d} and a support composition c of d+2 put

    W_phi(c) = (d+1)! * G(c) * ( E phi(F_c) - E phi(X_d) ),

where G(c) = U_c * prod(n_i - 1), F_c = (sum of independent uniforms on
{1..n_i-1}) - 1 is the flag distribution in Cheng-Lin's decomposition
CH_M = sum_J N_J P_J, and X_d is the Eulerian (Boolean matroid) distribution.
A nonnegative flow on the support split-DAG with divergence W_phi writes
"E phi(X_M) <= E phi(X_d)" as a nonnegative combination of the monotonicity
inequalities of Cheng-Lin Lemma 3.29.  By max-flow/min-cut (RESEARCH_NOTES.md,
Propositions 2 and 3, whose proofs use only that the weight vanishes off the
support) such a flow exists iff every ancestor-closed set of support
compositions has nonnegative W_phi-sum.

AFFINE INVARIANCE.  Every F_c and X_d has mean d/2 (and total mass one), so
W_phi = W_psi whenever phi - psi is affine.  In particular the generators
tail_phi / shell_phi below need not be symmetric as functions: their mirror
images differ from them by an affine function and give the same weight.

Everything is exact integer arithmetic.
"""

import os
import sys
from functools import lru_cache, reduce
from math import comb, factorial, gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dinic import Dinic  # noqa: E402
from k4_weights import u_value  # noqa: E402
from support import split_edges, support_compositions  # noqa: E402


def eulerian(n: int) -> list[int]:
    """A(n, j), j = 0..n-1: permutations of [n] with j descents."""
    row = [1]
    for m in range(2, n + 1):
        row = [(j + 1) * (row[j] if j < len(row) else 0)
               + (m - j) * (row[j - 1] if j >= 1 else 0) for j in range(m)]
    return row


@lru_cache(maxsize=None)
def _block_counts(sorted_parts: tuple[int, ...]) -> tuple[int, ...]:
    poly = [1]
    for n in sorted_parts:
        new = [0] * (len(poly) + n - 1)
        for a, ca in enumerate(poly):
            if ca:
                for y in range(1, n):
                    new[a + y] += ca
        poly = new
    return tuple(poly)


def flag_counts(c: tuple[int, ...]) -> tuple[int, ...]:
    """#{(y_i) : y_i in 1..n_i-1, sum y_i - 1 = p}, indexed by p >= 0."""
    return _block_counts(tuple(sorted(c)))[1:]


# ----------------------------------------------------------------- functionals

def moment_phi(d: int, k: int) -> list[int]:
    """(2p - d)^k = 2^k (p - d/2)^k."""
    return [(2 * p - d) ** k for p in range(d + 1)]


def hinge_phi(d: int, a: int) -> list[int]:
    return [max(p - a, 0) for p in range(d + 1)]


def shell_values(d: int) -> list[int]:
    """Attained values of |2a - d| for interior points a = 1..d-1."""
    return list(range(d % 2, d - 1, 2))


def from_second_difference(d: int, lam: list[int]) -> list[int]:
    """The function sum_{a=1}^{d-1} lam[a] (p - a)_+ ; its second difference at
    a is lam[a].  Any phi equals this plus an affine function."""
    return [sum(lam[a] * max(p - a, 0) for a in range(1, d)) for p in range(d + 1)]


def tail_phi(d: int, m: int) -> list[int]:
    """Second difference 1 where |2a - d| >= m, else 0."""
    return from_second_difference(d, [1 if abs(2 * a - d) >= m else 0 for a in range(d + 1)])


def shell_phi(d: int, m: int) -> list[int]:
    """Second difference 1 where |2a - d| == m, else 0.  For the innermost
    shell this is |2p - d| up to a positive factor and an affine function,
    i.e. the mean absolute deviation."""
    return from_second_difference(d, [1 if abs(2 * a - d) == m else 0 for a in range(d + 1)])


def exp_phi(d: int, x: int) -> list[int]:
    return [x ** p + x ** (d - p) for p in range(d + 1)]


def second_difference(phi: list[int]) -> list[int]:
    d = len(phi) - 1
    return [0] + [phi[a + 1] - 2 * phi[a] + phi[a - 1] for a in range(1, d)] + [0]


def is_affine(phi: list[int]) -> bool:
    return all(x == 0 for x in second_difference(phi))


def tail_decomposition(phi: list[int]) -> dict[int, int] | None:
    """Coefficients mu_m >= 0 with  phi = sum_m mu_m * tail_phi(d, m) + affine,
    or None if phi is not symmetric-convex with outward-nondecreasing second
    difference.  The identity is verified exactly before returning."""
    d = len(phi) - 1
    lam = second_difference(phi)
    ms = shell_values(d)
    by_shell = {}
    for a in range(1, d):
        m = abs(2 * a - d)
        if by_shell.setdefault(m, lam[a]) != lam[a]:
            return None  # second difference not symmetric
    mu, prev = {}, 0
    for m in ms:
        step = by_shell[m] - prev
        if step < 0:
            return None
        mu[m], prev = step, by_shell[m]
    combo = [0] * (d + 1)
    for m, coef in mu.items():
        t = tail_phi(d, m)
        combo = [x + coef * y for x, y in zip(combo, t)]
    assert is_affine([x - y for x, y in zip(phi, combo)])
    return mu


def moment_second_difference(d: int, k: int, a: int) -> int:
    """Closed form: the second difference of (2p-d)^k at a is
    2 * sum_{j>=1} C(k, 2j) 2^(2j) (2a-d)^(k-2j), a polynomial in (2a-d)^2
    with nonnegative coefficients when k is even."""
    return 2 * sum(comb(k, 2 * j) * 2 ** (2 * j) * (2 * a - d) ** (k - 2 * j)
                   for j in range(1, k // 2 + 1))


# ----------------------------------------------------------------- one dimension

class Level:
    """All data for one d: support compositions, split edges, flag counts."""

    def __init__(self, d: int):
        self.d = d
        self.comps = support_compositions(d)
        self.index = {c: k for k, c in enumerate(self.comps)}
        self.splits = {c: list(split_edges(c)) for c in self.comps}
        self.eulerian = eulerian(d + 1)
        self.fact = factorial(d + 1)
        self.U = {c: u_value(c, d) for c in self.comps}
        self.prod = {}
        for c in self.comps:
            pr = 1
            for m in c:
                pr *= m - 1
            self.prod[c] = pr
        self.cnt = {c: flag_counts(c) for c in self.comps}

    def boolean_identity_holds(self) -> bool:
        """sum_c U_c #{F_c = p} == A(d+1, p): the Boolean matroid (N_J = U_J)
        reproduces the Eulerian numbers."""
        tot = [0] * (self.d + 1)
        for c in self.comps:
            for p, x in enumerate(self.cnt[c]):
                tot[p] += self.U[c] * x
        return tot == self.eulerian

    def weights(self, phi: list[int]) -> dict[tuple[int, ...], int]:
        s_bool = sum(a * f for a, f in zip(self.eulerian, phi))
        out = {}
        for c in self.comps:
            s_c = sum(x * phi[p] for p, x in enumerate(self.cnt[c]))
            out[c] = self.U[c] * (self.fact * s_c - self.prod[c] * s_bool)
        return out

    def edges(self, width: int | None = None):
        for c in self.comps:
            for (i, p, child) in self.splits[c]:
                if width is None or min(p, c[i] - p) <= width:
                    yield c, i, p, child

    def solve(self, weights, width: int | None = None, want: str | None = None):
        """Exact max-flow.  Returns a dict with keys feasible, scale,
        total_supply, max_flow (the last two after dividing all weights by
        `scale`, their gcd) and, on request, `flow` (list of
        [parent, child, value] in scaled units, feasible case) or
        `cut_generators` (minimal elements of the descendant-closed source
        side, infeasible case)."""
        scale = reduce(gcd, (abs(v) for v in weights.values() if v), 0) or 1
        total = sum(v // scale for v in weights.values() if v > 0)
        inf = total + 1
        n = len(self.comps)
        src, snk = n, n + 1
        g = Dinic(n + 2)
        for c in self.comps:
            v = weights[c] // scale
            if v > 0:
                g.add_edge(src, self.index[c], v)
            elif v < 0:
                g.add_edge(self.index[c], snk, -v)
        inner = []
        for c, i, p, child in self.edges(width):
            inner.append((g.add_edge(self.index[c], self.index[child], inf), c, child))
        value = g.max_flow(src, snk)
        res = {"feasible": value == total, "scale": scale,
               "total_supply": total, "max_flow": value}
        if want == "certificate":
            if res["feasible"]:
                agg = {}
                for eid, c, child in inner:
                    used = inf - g.cap[eid]
                    if used:
                        agg[(c, child)] = agg.get((c, child), 0) + used
                res["flow"] = [[list(u), list(v), x] for (u, v), x in sorted(agg.items())]
            else:
                side = g.min_cut_source_side(src)
                inside = {c for c in self.comps if side[self.index[c]]}
                parents = {c: set() for c in self.comps}
                for c, i, p, child in self.edges(width):
                    parents[child].add(c)
                res["cut_generators"] = [list(c) for c in self.comps
                                         if c in inside and not (parents[c] & inside)]
        return res


# ------------------------------------------------- independent certificate checks

def check_flow(level: Level, weights, scale: int, flow, width: int | None = None) -> bool:
    """A flow certificate is valid iff every entry is a positive amount on a
    legal split edge and outflow - inflow == weight / scale at every node.
    Uses no max-flow code."""
    legal = {(c, child) for c, i, p, child in level.edges(width)}
    div = {c: 0 for c in level.comps}
    for u, v, x in flow:
        u, v = tuple(u), tuple(v)
        if (u, v) not in legal or x <= 0:
            return False
        div[u] += x
        div[v] -= x
    return all(div[c] * scale == weights[c] for c in level.comps)


def check_cut(level: Level, weights, generators, width: int | None = None) -> bool:
    """An infeasibility certificate: D = complement of the descendant closure
    of `generators` is ancestor-closed by construction, and its weight sum is
    negative.  Uses no max-flow code."""
    children = {c: [] for c in level.comps}
    for c, i, p, child in level.edges(width):
        children[c].append(child)
    seen = set()
    stack = [tuple(g) for g in generators]
    while stack:
        c = stack.pop()
        if c in seen:
            continue
        if c not in children:
            return False
        seen.add(c)
        stack.extend(children[c])
    return sum(weights[c] for c in level.comps if c not in seen) < 0


def min_ideal_sum(level: Level, weights) -> tuple[int, int]:
    """Brute force over ALL ancestor-closed sets (small d only): returns
    (minimum weight sum, number of sets).  Feasible iff the minimum is >= 0."""
    order = sorted(level.comps, key=lambda c: (len(c), c))
    pos = {c: i for i, c in enumerate(order)}
    par = [[] for _ in order]
    for c in order:
        for (_, _, child) in level.splits[c]:
            par[pos[child]].append(pos[c])
    w = [weights[c] for c in order]
    n = len(order)
    inset = [False] * n
    best = [0]
    count = [0]

    def rec(i: int, s: int) -> None:
        if i == n:
            count[0] += 1
            if s < best[0]:
                best[0] = s
            return
        rec(i + 1, s)
        if all(inset[q] for q in par[i]):
            inset[i] = True
            rec(i + 1, s + w[i])
            inset[i] = False

    rec(0, 0)
    return best[0], count[0]
