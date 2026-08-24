"""Independent small-network tests for exact deterministic min-cost flow."""

from itertools import product

from min_cost_flow import MinCostFlow


def brute_min_cost_max_flow(n, edges, source, sink, flow_limit=None):
    """Enumerate every integral edge flow; used only as a tiny oracle."""
    best_flow = -1
    best_cost = None
    for candidate in product(*(range(cap + 1) for _, _, cap, _ in edges)):
        div = [0] * n
        cost = 0
        for amount, (u, v, _, unit_cost) in zip(candidate, edges):
            div[u] += amount
            div[v] -= amount
            cost += amount * unit_cost
        value = div[source]
        if value < 0 or div[sink] != -value:
            continue
        if any(div[v] != 0 for v in range(n) if v not in (source, sink)):
            continue
        if flow_limit is not None and value > flow_limit:
            continue
        if value > best_flow or (value == best_flow and cost < best_cost):
            best_flow = value
            best_cost = cost
    return best_flow, best_cost


def test_exact_max_flow_and_minimum_cost_with_residual_rerouting():
    # The first cheapest path is s-a-x-t.  To attain the optimum at flow 2,
    # the algorithm must later cancel a->x along its negative-cost residual
    # reverse edge and finish with a->y and b->x.
    #
    #       a --1--> x
    #      / \       \
    #     s   2       t
    #      \   \     /
    #       b --1--> y       (b->y has cost 100)
    edges = [
        (0, 1, 1, 0),  # s -> a
        (0, 2, 1, 0),  # s -> b
        (1, 3, 1, 1),  # a -> x, initially chosen then cancelled
        (1, 4, 1, 2),  # a -> y
        (2, 3, 1, 1),  # b -> x
        (2, 4, 1, 100),  # b -> y
        (3, 5, 1, 0),  # x -> t
        (4, 5, 1, 0),  # y -> t
    ]
    expected = brute_min_cost_max_flow(6, edges, 0, 5)
    assert expected == (2, 3)

    graph = MinCostFlow(6)
    eids = [graph.add_edge(*edge) for edge in edges]
    result = graph.min_cost_max_flow(0, 5)

    assert (result.flow, result.cost) == expected
    assert [graph.flow_on(eid) for eid in eids] == [1, 1, 0, 1, 1, 0, 1, 1]
    assert result.cost == sum(
        graph.flow_on(eid) * edge[3] for eid, edge in zip(eids, edges)
    )


def test_flow_limit_and_parallel_ties_use_insertion_order():
    edges = [
        (0, 1, 1, 0),
        (0, 1, 1, 0),
        (0, 1, 1, 0),
    ]
    expected = brute_min_cost_max_flow(2, edges, 0, 1, flow_limit=2)
    assert expected == (2, 0)

    graph = MinCostFlow(2)
    eids = [graph.add_edge(*edge) for edge in edges]
    result = graph.min_cost_max_flow(0, 1, flow_limit=2)

    assert (result.flow, result.cost) == expected
    assert graph.flows() == {eids[0]: 1, eids[1]: 1, eids[2]: 0}


def test_cheapest_parallel_capacity_is_used_first():
    edges = [
        (0, 1, 3, 7),
        (0, 1, 1, 2),
        (0, 1, 2, 4),
    ]
    expected = brute_min_cost_max_flow(2, edges, 0, 1, flow_limit=4)
    assert expected == (4, 17)

    graph = MinCostFlow(2)
    eids = [graph.add_edge(*edge) for edge in edges]
    result = graph.min_cost_max_flow(0, 1, flow_limit=4)

    assert (result.flow, result.cost) == expected
    assert [graph.flow_on(eid) for eid in eids] == [1, 1, 2]


def test_capacities_and_costs_remain_exact_beyond_float_precision():
    capacity = 10**24 + 17
    unit_cost = 10**21 + 9
    graph = MinCostFlow(2)
    eid = graph.add_edge(0, 1, capacity, unit_cost)

    result = graph.min_cost_max_flow(0, 1)

    assert result.flow == capacity
    assert result.cost == capacity * unit_cost
    assert graph.flow_on(eid) == capacity
