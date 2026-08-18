"""Exact max-flow formulations of Conjecture 3.30.

Two networks, both with exact integer capacities:

* full_lattice_flow(d): nodes = all 2^d subsets of [d]; every Boolean cover
  edge J -> J u {j} with a rigorously safe "infinite" capacity
  INF = 1 + sum_{w>0} w_J  (any cut containing such an edge exceeds the
  trivial cut through the source edges, so no minimum cut uses one, and no
  flow can exceed total supply).  Source -> J (cap w_J) for w_J > 0,
  J -> sink (cap -w_J) for w_J < 0.  Only for small d (2^d nodes).

* support_flow(d): the reduced DAG on compositions of d+2 with all parts
  >= 2 (see support.py); equivalent by the reduction proved in
  RESEARCH_NOTES.md.  Scales to d >= 20.

Feasibility of Conjecture 3.30's flow certificate  <=>  max-flow == total
supply sum_{w>0} w_J.
"""

from dinic import Dinic
from support import split_edges, support_weights
from weights_bitmask import weight_map


class FlowResult:
    def __init__(self, total_supply, max_flow, dinic, source, sink, meta):
        self.total_supply = total_supply
        self.max_flow = max_flow
        self.feasible = max_flow == total_supply
        self.deficit = total_supply - max_flow
        self.dinic = dinic
        self.source = source
        self.sink = sink
        self.meta = meta  # network-specific labels


def full_lattice_flow(d: int) -> FlowResult:
    wm = weight_map(d)
    total_supply = sum(w for (_, _, w) in wm.values() if w > 0)
    inf = total_supply + 1
    n_nodes = (1 << d) + 2
    source, sink = 1 << d, (1 << d) + 1
    g = Dinic(n_nodes)
    cover_eids = {}  # (mask, j) -> edge id
    for mask in range(1 << d):
        w = wm[mask][2]
        if w > 0:
            g.add_edge(source, mask, w)
        elif w < 0:
            g.add_edge(mask, sink, -w)
        for j in range(1, d + 1):
            bit = 1 << (j - 1)
            if not mask & bit:
                cover_eids[(mask, j)] = g.add_edge(mask, mask | bit, inf)
    value = g.max_flow(source, sink)
    assert value <= total_supply
    return FlowResult(total_supply, value, g, source, sink,
                      {"weights": wm, "cover_eids": cover_eids, "d": d})


def build_support_network(d: int, edge_order=None, edge_filter=None):
    """Returns (g, source, sink, comps, index, sw, edge_labels, total_supply).

    edge_order: optional callable (parts, i, p, child) -> sort key, applied to
    each node's outgoing split edges before insertion.  Dinic prefers edges in
    insertion order, so this deterministically steers which certificate flow
    is found (Stage 3), without affecting the max-flow value.

    edge_filter: optional callable (parts, i, p, child) -> bool; when given,
    only splits with a True value are added.  Restricting edges can only
    lower the max flow, so feasibility of a restricted network is a
    *structural theorem candidate* (Stage 3); infeasibility just kills the
    hypothesis.
    """
    sw = support_weights(d)
    comps = sorted(sw)  # deterministic node order (lex on compositions)
    index = {c: k for k, c in enumerate(comps)}
    total_supply = sum(v[2] for v in sw.values() if v[2] > 0)
    inf = total_supply + 1
    source, sink = len(comps), len(comps) + 1
    g = Dinic(len(comps) + 2)
    edge_labels = {}  # eid -> (parent_comp, i, p) meaning split n_i -> (p, n_i-p)
    for c in comps:
        w = sw[c][2]
        if w > 0:
            g.add_edge(source, index[c], w)
        elif w < 0:
            g.add_edge(index[c], sink, -w)
        splits = list(split_edges(c))
        if edge_filter is not None:
            splits = [t for t in splits if edge_filter(c, t[0], t[1], t[2])]
        if edge_order is not None:
            splits.sort(key=lambda t: edge_order(c, t[0], t[1], t[2]))
        for i, p, child in splits:
            eid = g.add_edge(index[c], index[child], inf)
            edge_labels[eid] = (c, i, p)
    return g, source, sink, comps, index, sw, edge_labels, total_supply


def support_flow(d: int, edge_order=None, edge_filter=None) -> FlowResult:
    g, source, sink, comps, index, sw, edge_labels, total_supply = (
        build_support_network(d, edge_order, edge_filter)
    )
    value = g.max_flow(source, sink)
    assert value <= total_supply
    return FlowResult(total_supply, value, g, source, sink,
                      {"comps": comps, "index": index, "weights": sw,
                       "edge_labels": edge_labels, "d": d})
