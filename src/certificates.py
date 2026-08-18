"""Stage 3 tooling.

1. Structurally distinct integral certificates: run Dinic under different
   deterministic edge orderings (Dinic explores edges in insertion order, so
   the ordering steers which max flow is found; the value never changes).

2. Edge-restricted feasibility tests: delete all split edges outside a
   structural family and ask whether the certificate survives.  A family that
   stays feasible for every d is a structural theorem candidate.

3. Tight cuts via Picard-Queyranne: the family of minimum cuts (equivalently,
   of *tight ideals*, i.e. down-closed D with sum_D w = 0) is exactly the
   family of residual-closed source sets, which is flow-independent.  We
   compute the SCC condensation of the residual graph and sample closed sets.

Edge vocabulary: an edge is (c, i, p): composition c splits part n_i = c[i]
into (p, n_i - p), giving child c[:i] + (p, n_i-p) + c[i+1:].  In subset
language this adds the element j = (prefix sum of c[:i]) + p to J.
"""

from flows import support_flow

# ---------------------------------------------------------------------------
# 1. edge-order heuristics -> structurally distinct certificates
# ---------------------------------------------------------------------------

HEURISTICS = {
    # split earliest block first, then smallest left piece
    "early_small": lambda c, i, p, ch: (i, p),
    # split latest block first
    "late_small": lambda c, i, p, ch: (-i, p),
    # balanced splits first (|2p - n_i| small), tie: earlier block
    "balanced": lambda c, i, p, ch: (abs(2 * p - c[i]), i, p),
    # extreme splits first (peel small pieces), tie: later block
    "unbalanced": lambda c, i, p, ch: (-abs(2 * p - c[i]), -i, p),
}


def extract_certificate(d: int, heuristic: str):
    """Solve with the given edge-order heuristic; return (res, flow_edges)
    where flow_edges = [(c, i, p, f)] with f > 0.  Asserts feasibility and
    the divergence identity div f = w (so the output IS a certificate)."""
    res = support_flow(d, edge_order=HEURISTICS[heuristic])
    assert res.feasible, f"d={d} infeasible?! deficit={res.deficit}"
    g, meta = res.dinic, res.meta
    sw = meta["weights"]
    flow_edges = []
    div = {c: 0 for c in sw}
    for eid, (c, i, p) in meta["edge_labels"].items():
        f = g.flow_on(eid)
        assert f >= 0
        child = c[:i] + (p, c[i] - p) + c[i + 1 :]
        div[c] += f
        div[child] -= f
        if f > 0:
            flow_edges.append((c, i, p, f))
    for c, (_, _, w) in sw.items():
        assert div[c] == w, (d, heuristic, c)
    return res, flow_edges


# ---------------------------------------------------------------------------
# 2. edge-restricted structural families
# ---------------------------------------------------------------------------

RESTRICTIONS = {
    # only split (one of) the largest parts
    "largest_block": lambda c, i, p, ch: c[i] == max(c),
    # only split the first part
    "first_block": lambda c, i, p, ch: i == 0,
    # only split the last part
    "last_block": lambda c, i, p, ch: i == len(c) - 1,
    # only peel a piece of size 2 off either end of a part
    "peel2": lambda c, i, p, ch: p == 2 or c[i] - p == 2,
    # only peel a 2 off the left end of a part
    "peel2_left": lambda c, i, p, ch: p == 2,
    # only peel 2 or 3 off either end
    "peel23": lambda c, i, p, ch: p in (2, 3) or c[i] - p in (2, 3),
    # only balanced splits: |p - (n_i - p)| <= 1
    "balanced_only": lambda c, i, p, ch: abs(2 * p - c[i]) <= 1,
    # largest part AND peel-2
    "largest_peel2": lambda c, i, p, ch: c[i] == max(c)
    and (p == 2 or c[i] - p == 2),
}


def restricted_feasible(d: int, restriction: str):
    """(feasible, deficit) for the edge-restricted network."""
    res = support_flow(d, edge_filter=RESTRICTIONS[restriction])
    return res.feasible, res.deficit


# ---------------------------------------------------------------------------
# 3. tight cuts (Picard-Queyranne)
# ---------------------------------------------------------------------------

def _residual_adj(res):
    """Adjacency (list of lists) of the residual graph of a solved network."""
    g = res.dinic
    adj = [[] for _ in range(g.n)]
    for eid in range(0, len(g.to), 2):
        u, v = g.to[eid ^ 1], g.to[eid]
        if g.cap[eid] > 0:
            adj[u].append(v)
        if g.cap[eid ^ 1] > 0:
            adj[v].append(u)
    return adj


def _sccs(adj):
    """Iterative Tarjan; returns comp[] labels in reverse topological order
    (comp of u < comp of v whenever the condensation has edge u-scc -> v-scc
    ... labels are assigned so that every condensation edge goes from a
    higher label to a lower label)."""
    n = len(adj)
    index = [-1] * n
    low = [0] * n
    on = [False] * n
    comp = [-1] * n
    stack: list[int] = []
    counter = [0]
    ncomp = [0]
    for root in range(n):
        if index[root] != -1:
            continue
        work = [(root, 0)]
        while work:
            u, ei = work.pop()
            if ei == 0:
                index[u] = low[u] = counter[0]
                counter[0] += 1
                stack.append(u)
                on[u] = True
            recurse = False
            while ei < len(adj[u]):
                v = adj[u][ei]
                ei += 1
                if index[v] == -1:
                    work.append((u, ei))
                    work.append((v, 0))
                    recurse = True
                    break
                if on[v]:
                    low[u] = min(low[u], index[v])
            if recurse:
                continue
            if low[u] == index[u]:
                while True:
                    v = stack.pop()
                    on[v] = False
                    comp[v] = ncomp[0]
                    if v == u:
                        break
                ncomp[0] += 1
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[u])
    return comp, ncomp[0]


def tight_cut_structure(d: int, max_samples: int = 20):
    """Solve d; return dict describing the family of tight ideals:
    number of residual SCCs, the minimal/maximal tight ideals, and a sample
    of distinct nontrivial tight ideals (as lists of compositions)."""
    res = support_flow(d)
    assert res.feasible
    g, meta = res.dinic, res.meta
    comps, index = meta["comps"], meta["index"]
    sw = meta["weights"]
    adj = _residual_adj(res)
    comp, ncomp = _sccs(adj)

    # condensation successors
    succ = [set() for _ in range(ncomp)]
    for u in range(g.n):
        for v in adj[u]:
            if comp[u] != comp[v]:
                succ[comp[u]].add(comp[v])

    s_scc, t_scc = comp[res.source], comp[res.sink]

    def closure(seed_sccs):
        """SCCs reachable from seed set (residual-forward closure)."""
        seen = set(seed_sccs)
        stack = list(seed_sccs)
        while stack:
            x = stack.pop()
            for y in succ[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    def ideal_of(source_side_sccs):
        """Lattice complement of the source side = tight ideal."""
        return [c for c in comps if comp[index[c]] not in source_side_sccs]

    base = closure({s_scc})
    assert t_scc not in base, "residual s->t path after max flow?!"
    maximal_ideal = ideal_of(base)  # minimal source side -> maximal ideal
    # maximal source side = everything not reaching t:
    reach_t = {x for x in range(ncomp) if t_scc in closure({x})}
    minimal_ideal = ideal_of({x for x in range(ncomp) if x not in reach_t})

    samples = []
    seen_keys = set()
    for x in range(ncomp):
        if x == t_scc or x in base or x in reach_t:
            continue
        cl = closure(base | {x})
        if t_scc in cl:
            continue
        ideal = ideal_of(cl)
        key = frozenset(map(tuple, ideal))
        if key not in seen_keys:
            seen_keys.add(key)
            samples.append(ideal)
        if len(samples) >= max_samples:
            break

    def summarize(ideal):
        return {
            "size": len(ideal),
            "weight_sum": sum(sw[c][2] for c in ideal),
            "compositions": [list(c) for c in ideal] if len(ideal) <= 40 else None,
        }

    return {
        "d": d,
        "n_support_nodes": len(comps),
        "n_residual_sccs": ncomp,
        "minimal_tight_ideal": summarize(minimal_ideal),
        "maximal_tight_ideal": summarize(maximal_ideal),
        "n_nontrivial_samples": len(samples),
        "nontrivial_tight_ideal_samples": [summarize(i) for i in samples[:5]],
    }
