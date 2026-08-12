"""Small-d cross-validation of three independent decision procedures:

1. brute-force minimum over ALL down-closed ideals (d <= 5 only);
2. exact max-flow on the FULL Boolean-lattice network;
3. exact max-flow on the reduced support DAG.

They must agree exactly (value, feasibility, deficit)."""

import pytest

from flows import full_lattice_flow, support_flow
from ideals import min_ideal_sum


@pytest.mark.parametrize("d", range(1, 6))
def test_ideal_oracle_vs_flows(d):
    best, best_ideal, count = min_ideal_sum(d)
    lat = full_lattice_flow(d)
    sup = support_flow(d)
    assert best <= 0  # the empty ideal gives 0
    # LP duality (proved in RESEARCH_NOTES.md): deficit = -min ideal sum
    assert lat.deficit == -best, (d, lat.deficit, best)
    assert sup.deficit == -best, (d, sup.deficit, best)
    assert lat.feasible == sup.feasible == (best == 0)


# Stage 1 scope: d <= 5 (extend after the first decision gate).
@pytest.mark.parametrize("d", range(1, 6))
def test_lattice_flow_equals_support_flow(d):
    lat = full_lattice_flow(d)
    sup = support_flow(d)
    assert lat.total_supply == sup.total_supply
    assert lat.max_flow == sup.max_flow, (d, lat.max_flow, sup.max_flow)


@pytest.mark.parametrize("d", range(1, 6))
def test_flow_conservation_and_divergence(d):
    """A max flow on the support DAG, if feasible, gives divergence w_J at
    every support node (out - in over cover edges = w_J)."""
    res = support_flow(d)
    if not res.feasible:
        pytest.skip("infeasible; divergence identity only for certificates")
    g, meta = res.dinic, res.meta
    index, sw = meta["index"], meta["weights"]
    div = {c: 0 for c in index}
    for eid, (parent, i, p) in meta["edge_labels"].items():
        f = g.flow_on(eid)
        assert f >= 0
        div[parent] += f
        child = parent[:i] + (p, parent[i] - p) + parent[i + 1 :]
        div[child] -= f
    for c, (_, _, w) in sw.items():
        assert div[c] == w, (d, c, div[c], w)
