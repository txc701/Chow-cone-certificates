"""Exact certificates on the k=4 peel-width-at-most-3 support DAG.

This module is deliberately k=4-specific.  It uses the repository's exact
integer fourth-moment weights, but it does not change the older k=2 flow
machinery.  A certificate is a nonnegative flow on composition-splitting
cover edges whose divergence is ``w4`` at every support composition.

The max-flow output is deterministic once an ``EDGE_ORDERS`` strategy is
named: support nodes are lexicographically ordered, outgoing cover edges are
sorted by the named total key, and Dinic traverses adjacency lists in
insertion order.  The persisted representation is sparse (positive cover
flows only) and stores unbounded integers as decimal strings.

``edgewise_ranges`` controls certificate nonuniqueness more strongly than
sampling solver outputs.  Starting from any feasible flow, it computes the
exact minimum and maximum of every allowed edge coordinate by residual
rerouting.  This is practical for the intended d <= 10 audit range.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Callable, Mapping

from dinic import Dinic
from k4_weights import support_w4
from min_cost_flow import MinCostFlow
from support import support_compositions


Composition = tuple[int, ...]
EdgeKey = tuple[Composition, int, int]
EdgeOrderKey = Callable[[Composition, int, int, Composition], tuple]
CostProfile = Callable[[int, Composition, int, int, Composition], int]

SCHEMA = "chow-cone/k4-peel-width-certificate/v1"
PEEL_WIDTH_MAX = 3
WEIGHT_SCALE = 720


def _peel_width(parent: Composition, block: int, left: int) -> int:
    return min(left, parent[block] - left)


EDGE_ORDERS: dict[str, EdgeOrderKey] = {
    "lex": lambda c, i, p, child: (i, p, child),
    "reverse_lex": lambda c, i, p, child: (
        -i,
        -p,
        tuple(-x for x in child),
    ),
    "peel_width_then_lex": lambda c, i, p, child: (
        _peel_width(c, i, p),
        i,
        p,
        child,
    ),
    "wide_peel_then_lex": lambda c, i, p, child: (
        -_peel_width(c, i, p),
        i,
        p,
        child,
    ),
    "late_block_then_lex": lambda c, i, p, child: (-i, p, child),
    "balanced_then_lex": lambda c, i, p, child: (
        abs(2 * p - c[i]),
        i,
        p,
        child,
    ),
}

EDGE_ORDER_DESCRIPTIONS = {
    "lex": "(block_index, left_part, child_composition)",
    "reverse_lex": "reverse (block_index, left_part, child_composition)",
    "peel_width_then_lex": "(peel_width, block_index, left_part, child)",
    "wide_peel_then_lex": "(-peel_width, block_index, left_part, child)",
    "late_block_then_lex": "(-block_index, left_part, child)",
    "balanced_then_lex": "(|2*left-block_size|, block_index, left_part, child)",
}


def _added_cut_position(
    d: int,
    parent: Composition,
    block: int,
    left: int,
    child: Composition,
) -> int:
    del child
    position = sum(parent[:block]) + left
    if not 1 <= position <= d:
        raise CertificateGenerationError(
            f"invalid added cut position {position} for d={d}"
        )
    return position


COST_PROFILES: dict[str, CostProfile] = {
    "total_internal_flow": lambda d, c, i, p, child: 1,
    "peel3_mass": lambda d, c, i, p, child: int(_peel_width(c, i, p) == 3),
    "final_block_mass": lambda d, c, i, p, child: int(i == len(c) - 1),
    "first_block_mass": lambda d, c, i, p, child: int(i == 0),
    "balanced_split_mass": lambda d, c, i, p, child: int(2 * p == c[i]),
    "right_peel_mass": lambda d, c, i, p, child: int(p > c[i] - p),
    "added_cut_position": _added_cut_position,
    "reflected_position": lambda d, c, i, p, child: (
        d + 1 - _added_cut_position(d, c, i, p, child)
    ),
}

COST_PROFILE_DEFINITIONS = {
    "total_internal_flow": "sum_e f(e): unit cost 1 on every internal cover edge",
    "peel3_mass": (
        "sum_{e: min(left,right)=3} f(e): cost 1 on width-3 peels, 0 otherwise"
    ),
    "final_block_mass": (
        "sum_{e: block=len(parent)-1} f(e): cost 1 on final-block splits, "
        "0 otherwise"
    ),
    "first_block_mass": (
        "sum_{e: block=0} f(e): cost 1 on first-block splits, 0 otherwise"
    ),
    "balanced_split_mass": (
        "sum_{e: left=right} f(e): cost 1 on balanced splits, 0 otherwise"
    ),
    "right_peel_mass": (
        "sum_{e: left>right} f(e): cost 1 when the narrow peel is on the "
        "right, 0 otherwise"
    ),
    "added_cut_position": (
        "sum_e j(e) f(e), where j(e)=sum(parent[:block])+left"
    ),
    "reflected_position": (
        "sum_e (d+1-j(e)) f(e), where j(e)=sum(parent[:block])+left"
    ),
}


class CertificateGenerationError(RuntimeError):
    """The restricted exact flow problem was infeasible or malformed."""


@dataclass(frozen=True)
class EdgeRange:
    """Exact feasible interval for one allowed edge coordinate."""

    minimum: int
    current: int
    maximum: int
    classification: str


@dataclass
class _Network:
    graph: Dinic
    source: int
    sink: int
    compositions: list[Composition]
    index: dict[Composition, int]
    weights: dict[Composition, int]
    edge_eids: dict[EdgeKey, int]
    total_supply: int


@dataclass
class _MinCostNetwork:
    graph: MinCostFlow
    source: int
    sink: int
    compositions: list[Composition]
    index: dict[Composition, int]
    weights: dict[Composition, int]
    edge_eids: dict[EdgeKey, int]
    edge_costs: dict[EdgeKey, int]
    total_supply: int


def _child(parent: Composition, block: int, left: int) -> Composition:
    size = parent[block]
    return parent[:block] + (left, size - left) + parent[block + 1 :]


def _outgoing_allowed(parent: Composition) -> list[tuple[int, int, Composition]]:
    out = []
    for block, size in enumerate(parent):
        for left in range(2, size - 1):
            if min(left, size - left) <= PEEL_WIDTH_MAX:
                out.append((block, left, _child(parent, block, left)))
    return out


def allowed_edge_keys(d: int, edge_order: str = "lex") -> list[EdgeKey]:
    """All peel-width <= 3 cover edges in a fully specified order."""
    if edge_order not in EDGE_ORDERS:
        raise ValueError(
            f"unknown edge order {edge_order!r}; expected one of "
            f"{sorted(EDGE_ORDERS)}"
        )
    key = EDGE_ORDERS[edge_order]
    out: list[EdgeKey] = []
    for parent in sorted(support_compositions(d)):
        edges = sorted(
            _outgoing_allowed(parent),
            key=lambda item: key(parent, item[0], item[1], item[2]),
        )
        out.extend((parent, block, left) for block, left, _ in edges)
    return out


def _build_network(d: int, edge_order: str) -> _Network:
    if not isinstance(d, int) or isinstance(d, bool) or d < 2:
        raise ValueError("d must be an integer at least 2")
    if edge_order not in EDGE_ORDERS:
        raise ValueError(
            f"unknown edge order {edge_order!r}; expected one of "
            f"{sorted(EDGE_ORDERS)}"
        )

    weights = support_w4(d)
    compositions = sorted(weights)
    index = {composition: i for i, composition in enumerate(compositions)}
    if sum(weights.values()) != 0:
        raise CertificateGenerationError(f"k=4 weights do not sum to zero at d={d}")
    total_supply = sum(weight for weight in weights.values() if weight > 0)
    cover_capacity = total_supply + 1
    source, sink = len(compositions), len(compositions) + 1
    graph = Dinic(len(compositions) + 2)
    edge_eids: dict[EdgeKey, int] = {}
    order_key = EDGE_ORDERS[edge_order]

    # This loop fixes source, sink, and cover-edge insertion order completely.
    for parent in compositions:
        node = index[parent]
        weight = weights[parent]
        if weight > 0:
            graph.add_edge(source, node, weight)
        elif weight < 0:
            graph.add_edge(node, sink, -weight)

        outgoing = sorted(
            _outgoing_allowed(parent),
            key=lambda item: order_key(parent, item[0], item[1], item[2]),
        )
        for block, left, child in outgoing:
            edge = (parent, block, left)
            if edge in edge_eids:
                raise CertificateGenerationError(f"duplicate cover edge: {edge}")
            edge_eids[edge] = graph.add_edge(
                node, index[child], cover_capacity
            )

    return _Network(
        graph=graph,
        source=source,
        sink=sink,
        compositions=compositions,
        index=index,
        weights=weights,
        edge_eids=edge_eids,
        total_supply=total_supply,
    )


def _build_min_cost_network(d: int, objective: str) -> _MinCostNetwork:
    """Build a lex-inserted exact network for one named secondary objective."""
    if not isinstance(d, int) or isinstance(d, bool) or d < 2:
        raise ValueError("d must be an integer at least 2")
    if objective not in COST_PROFILES:
        raise ValueError(
            f"unknown cost profile {objective!r}; expected one of "
            f"{sorted(COST_PROFILES)}"
        )

    weights = support_w4(d)
    compositions = sorted(weights)
    index = {composition: i for i, composition in enumerate(compositions)}
    if sum(weights.values()) != 0:
        raise CertificateGenerationError(f"k=4 weights do not sum to zero at d={d}")
    total_supply = sum(weight for weight in weights.values() if weight > 0)
    cover_capacity = total_supply + 1
    source, sink = len(compositions), len(compositions) + 1
    graph = MinCostFlow(len(compositions) + 2)
    edge_eids: dict[EdgeKey, int] = {}
    edge_costs: dict[EdgeKey, int] = {}
    cost_profile = COST_PROFILES[objective]

    # Node order is lexicographic, and each node's outgoing cover edges use
    # the literal structural order (block, left, child).  Thus objective ties
    # have deterministic insertion-order behaviour independent of dict order.
    for parent in compositions:
        node = index[parent]
        weight = weights[parent]
        if weight > 0:
            graph.add_edge(source, node, weight, 0)
        elif weight < 0:
            graph.add_edge(node, sink, -weight, 0)

        outgoing = sorted(
            _outgoing_allowed(parent),
            key=lambda item: (item[0], item[1], item[2]),
        )
        for block, left, child in outgoing:
            edge = (parent, block, left)
            cost = cost_profile(d, parent, block, left, child)
            if not isinstance(cost, int) or isinstance(cost, bool) or cost < 0:
                raise CertificateGenerationError(
                    f"cost profile {objective!r} returned invalid cost "
                    f"{cost!r} at {edge!r}"
                )
            edge_costs[edge] = cost
            edge_eids[edge] = graph.add_edge(
                node, index[child], cover_capacity, cost
            )

    return _MinCostNetwork(
        graph=graph,
        source=source,
        sink=sink,
        compositions=compositions,
        index=index,
        weights=weights,
        edge_eids=edge_eids,
        edge_costs=edge_costs,
        total_supply=total_supply,
    )


def _complete_flow(
    d: int, sparse_flow: Mapping[EdgeKey, int]
) -> tuple[list[EdgeKey], dict[EdgeKey, int], dict[Composition, int], int]:
    """Validate a sparse flow against canonical weights and fill zero edges."""
    edges = allowed_edge_keys(d)
    allowed = set(edges)
    unknown = set(sparse_flow) - allowed
    if unknown:
        raise ValueError(f"flow contains disallowed edge(s), first={min(unknown)!r}")

    weights = support_w4(d)
    total_supply = sum(weight for weight in weights.values() if weight > 0)
    flow: dict[EdgeKey, int] = {}
    divergence = {composition: 0 for composition in sorted(weights)}
    for edge in edges:
        value = sparse_flow.get(edge, 0)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"flow must be a nonnegative integer at {edge!r}")
        if value > total_supply:
            raise ValueError(f"flow exceeds total supply at {edge!r}")
        flow[edge] = value
        parent, block, left = edge
        child = _child(parent, block, left)
        divergence[parent] += value
        divergence[child] -= value

    mismatches = [
        (composition, divergence[composition], weights[composition])
        for composition in sorted(weights)
        if divergence[composition] != weights[composition]
    ]
    if mismatches:
        raise ValueError(f"flow is not feasible; first mismatch={mismatches[0]!r}")
    if sum(divergence.values()) != 0 or sum(weights.values()) != 0:
        raise ValueError("nonzero total divergence or total k=4 weight")
    return edges, flow, weights, total_supply


def solve_certificate(d: int, edge_order: str = "lex") -> dict[EdgeKey, int]:
    """Return one deterministic sparse exact certificate for ``d``.

    The returned mapping contains positive cover flows only.  It is an exact
    max-flow witness, not a claim that these coordinates are structural or
    invariant across all feasible certificates.
    """
    network = _build_network(d, edge_order)
    value = network.graph.max_flow(network.source, network.sink)
    if value != network.total_supply:
        raise CertificateGenerationError(
            f"peel-width <= 3 is infeasible at d={d}: "
            f"flow={value}, supply={network.total_supply}"
        )

    sparse: dict[EdgeKey, int] = {}
    for edge, eid in network.edge_eids.items():
        flow = network.graph.flow_on(eid)
        if flow < 0:
            raise CertificateGenerationError(f"negative extracted flow at {edge!r}")
        if flow > 0:
            sparse[edge] = flow
    _complete_flow(d, sparse)
    return sparse


def certificate_objective_value(
    d: int, sparse_flow: Mapping[EdgeKey, int], objective: str
) -> int:
    """Recompute one named linear objective directly from a feasible flow."""
    if objective not in COST_PROFILES:
        raise ValueError(
            f"unknown cost profile {objective!r}; expected one of "
            f"{sorted(COST_PROFILES)}"
        )
    edges, flow, _, _ = _complete_flow(d, sparse_flow)
    profile = COST_PROFILES[objective]
    value = 0
    for parent, block, left in edges:
        child = _child(parent, block, left)
        cost = profile(d, parent, block, left, child)
        if not isinstance(cost, int) or isinstance(cost, bool) or cost < 0:
            raise CertificateGenerationError(
                f"cost profile {objective!r} returned invalid cost {cost!r}"
            )
        value += cost * flow[(parent, block, left)]
    return value


def solve_min_cost_certificate(
    d: int, objective: str
) -> tuple[dict[EdgeKey, int], int]:
    """Return an exact minimum-cost feasible certificate and objective value.

    The network first maximizes source-to-sink flow up to ``total_supply``;
    among flows attaining that value it minimizes the named nonnegative
    integer cost.  Lexicographic node and edge insertion makes any remaining
    optimum tie deterministic.
    """
    network = _build_min_cost_network(d, objective)
    result = network.graph.min_cost_max_flow(
        network.source,
        network.sink,
        flow_limit=network.total_supply,
    )
    if result.flow != network.total_supply:
        raise CertificateGenerationError(
            f"peel-width <= 3 is infeasible at d={d}: "
            f"flow={result.flow}, supply={network.total_supply}"
        )

    sparse: dict[EdgeKey, int] = {}
    for edge, eid in network.edge_eids.items():
        flow = network.graph.flow_on(eid)
        if flow < 0:
            raise CertificateGenerationError(f"negative extracted flow at {edge!r}")
        if flow > 0:
            sparse[edge] = flow
    _complete_flow(d, sparse)
    recomputed = certificate_objective_value(d, sparse, objective)
    if recomputed != result.cost:
        raise CertificateGenerationError(
            f"objective mismatch for {objective!r}: "
            f"solver={result.cost}, recomputed={recomputed}"
        )
    return sparse, result.cost


def certificate_document(d: int, edge_order: str = "lex") -> dict:
    """Build the versioned sparse JSON-compatible certificate document."""
    sparse = solve_certificate(d, edge_order=edge_order)
    allowed, _, weights, total_supply = _complete_flow(d, sparse)
    positive_edges = [
        [list(parent), block, left, str(sparse[(parent, block, left)])]
        for parent, block, left in sorted(sparse)
    ]
    return {
        "schema": SCHEMA,
        "d": d,
        "peel_width_max": PEEL_WIDTH_MAX,
        "weight_scale": WEIGHT_SCALE,
        "generation": {
            "algorithm": "Dinic exact-integer max flow",
            "node_order": "lexicographic compositions",
            "edge_order": edge_order,
            "edge_order_key": EDGE_ORDER_DESCRIPTIONS[edge_order],
            "source_sink_order": "interleaved by lexicographic node order",
            "cover_capacity": "total_supply + 1",
            "flow_encoding": "sparse positive edges; decimal integer strings",
        },
        "n_support_nodes": len(weights),
        "n_allowed_edges": len(allowed),
        "n_positive_edges": len(positive_edges),
        "total_supply": str(total_supply),
        "edges": positive_edges,
    }


def min_cost_certificate_document(d: int, objective: str) -> dict:
    """Build a sparse schema-compatible exact minimum-cost certificate."""
    sparse, objective_value = solve_min_cost_certificate(d, objective)
    allowed, _, weights, total_supply = _complete_flow(d, sparse)
    positive_edges = [
        [list(parent), block, left, str(sparse[(parent, block, left)])]
        for parent, block, left in sorted(sparse)
    ]
    return {
        "schema": SCHEMA,
        "d": d,
        "peel_width_max": PEEL_WIDTH_MAX,
        "weight_scale": WEIGHT_SCALE,
        "generation": {
            "algorithm": (
                "successive-shortest-augmenting-path exact-integer "
                "minimum-cost maximum flow"
            ),
            "node_order": "lexicographic compositions",
            "edge_order": "lex",
            "edge_order_key": EDGE_ORDER_DESCRIPTIONS["lex"],
            "source_sink_order": "interleaved by lexicographic node order",
            "cover_capacity": "total_supply + 1",
            "flow_encoding": "sparse positive edges; decimal integer strings",
            "flow_requirement": "maximum flow equals total_supply",
            "tie_breaking": (
                "Dijkstra (distance,node); equal-distance relaxations retain "
                "first lex-inserted edge"
            ),
        },
        "objective": {
            "name": objective,
            "definition": COST_PROFILE_DEFINITIONS[objective],
            "value": str(objective_value),
            "unit_costs": "nonnegative integers on internal cover edges",
        },
        "n_support_nodes": len(weights),
        "n_allowed_edges": len(allowed),
        "n_positive_edges": len(positive_edges),
        "total_supply": str(total_supply),
        "edges": positive_edges,
    }


def write_certificate(path: str | Path, d: int, edge_order: str = "lex") -> dict:
    """Write a deterministic certificate document and return it."""
    document = certificate_document(d, edge_order=edge_order)
    with Path(path).open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return document


def write_min_cost_certificate(
    path: str | Path, d: int, objective: str
) -> dict:
    """Write a deterministic minimum-cost certificate document and return it."""
    document = min_cost_certificate_document(d, objective)
    with Path(path).open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return document


def _residual_reroute_amount(
    compositions: list[Composition],
    index: Mapping[Composition, int],
    edges: list[EdgeKey],
    flow: Mapping[EdgeKey, int],
    target: EdgeKey,
    total_supply: int,
    direction: str,
) -> int:
    """Maximum exact change of ``target`` in one direction.

    To decrease u->v by delta, route delta from u to v through the residual
    network with the target edge removed; the target's reverse completes a
    circulation.  To increase it, route from v to u and complete the
    circulation with the target's forward direction.  Every feasible
    difference is a residual circulation, so these maxima are exact.
    """
    parent, block, left = target
    child = _child(parent, block, left)
    if direction == "decrease":
        start, end = parent, child
        limit = flow[target]
    elif direction == "increase":
        start, end = child, parent
        limit = total_supply - flow[target]
    else:
        raise ValueError("direction must be 'decrease' or 'increase'")
    if limit == 0:
        return 0

    # Auxiliary source/sink impose the requested limit without changing the
    # shared Dinic implementation.
    aux_source, aux_sink = len(compositions), len(compositions) + 1
    graph = Dinic(len(compositions) + 2)
    graph.add_edge(aux_source, index[start], limit)
    graph.add_edge(index[end], aux_sink, limit)
    for edge in edges:
        if edge == target:
            continue
        edge_parent, edge_block, edge_left = edge
        edge_child = _child(edge_parent, edge_block, edge_left)
        value = flow[edge]
        forward_capacity = total_supply - value
        if forward_capacity:
            graph.add_edge(
                index[edge_parent], index[edge_child], forward_capacity
            )
        if value:
            graph.add_edge(index[edge_child], index[edge_parent], value)
    return graph.max_flow(aux_source, aux_sink)


def edgewise_ranges(
    d: int, sparse_flow: Mapping[EdgeKey, int]
) -> dict[EdgeKey, EdgeRange]:
    """Compute exact min/max of every allowed coordinate.

    The artificial upper bound ``total_supply`` is lossless: on this acyclic
    cover graph, any feasible nonnegative flow decomposes into paths carrying
    the total positive supply, hence no edge can carry more than that total.
    Running this for every edge is intentionally targeted at d <= 10.
    """
    edges, flow, weights, total_supply = _complete_flow(d, sparse_flow)
    compositions = sorted(weights)
    index = {composition: i for i, composition in enumerate(compositions)}
    ranges: dict[EdgeKey, EdgeRange] = {}
    for edge in edges:
        decrease = _residual_reroute_amount(
            compositions,
            index,
            edges,
            flow,
            edge,
            total_supply,
            "decrease",
        )
        increase = _residual_reroute_amount(
            compositions,
            index,
            edges,
            flow,
            edge,
            total_supply,
            "increase",
        )
        minimum = flow[edge] - decrease
        maximum = flow[edge] + increase
        if minimum == maximum == 0:
            classification = "fixed_zero"
        elif minimum == maximum:
            classification = "fixed_positive"
        elif minimum == 0:
            classification = "optional"
        else:
            classification = "forced_variable"
        if not (0 <= minimum <= flow[edge] <= maximum <= total_supply):
            raise CertificateGenerationError(
                f"invalid residual range at {edge!r}: "
                f"{minimum} <= {flow[edge]} <= {maximum}"
            )
        ranges[edge] = EdgeRange(
            minimum=minimum,
            current=flow[edge],
            maximum=maximum,
            classification=classification,
        )
    return ranges
