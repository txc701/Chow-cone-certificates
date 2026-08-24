"""Deterministic exact-integer minimum-cost maximum flow.

The implementation is the successive-shortest-augmenting-path algorithm.
Forward capacities and costs are nonnegative integers.  Residual reverse
edges have the negated cost; Johnson potentials keep every residual cost
seen by Dijkstra nonnegative.

Tie behaviour is deterministic: nodes are popped by ``(distance, node)``
and equal-distance relaxations retain the first edge encountered.  Thus a
fixed node numbering and edge insertion order produce a fixed optimum even
when the minimum-cost flow is not unique.
"""

from dataclasses import dataclass
from heapq import heappop, heappush


@dataclass(frozen=True)
class MinCostFlowResult:
    """Value and cost returned by :meth:`MinCostFlow.min_cost_max_flow`."""

    flow: int
    cost: int


class MinCostFlow:
    """Directed capacitated network with exact integer costs.

    Each call to :meth:`add_edge` returns an even edge id for the forward
    edge.  Its odd partner ``eid ^ 1`` is the residual reverse edge.
    A network is solved at most once; forward flows remain available through
    :meth:`flow_on` and :meth:`flows` afterward.
    """

    def __init__(self, n: int):
        if not isinstance(n, int) or n <= 0:
            raise ValueError("number of nodes must be a positive integer")
        self.n = n
        self.head: list[list[int]] = [[] for _ in range(n)]
        self.frm: list[int] = []
        self.to: list[int] = []
        self.cap: list[int] = []
        self.cost: list[int] = []
        self.initial_cap: list[int] = []
        self._solved = False

    def add_edge(self, u: int, v: int, cap: int, cost: int) -> int:
        """Add ``u -> v`` and return its forward edge id.

        ``cap`` and ``cost`` must be nonnegative integers.  Parallel edges
        are supported and retain their insertion order.
        """
        if not (isinstance(u, int) and isinstance(v, int)):
            raise TypeError("node ids must be integers")
        if not (0 <= u < self.n and 0 <= v < self.n):
            raise ValueError("node id out of range")
        if not isinstance(cap, int) or cap < 0:
            raise ValueError("capacity must be a nonnegative integer")
        if not isinstance(cost, int) or cost < 0:
            raise ValueError("forward cost must be a nonnegative integer")
        if self._solved:
            raise RuntimeError("cannot add an edge after solving")

        eid = len(self.to)
        self.head[u].append(eid)
        self.frm.append(u)
        self.to.append(v)
        self.cap.append(cap)
        self.cost.append(cost)
        self.initial_cap.append(cap)

        self.head[v].append(eid + 1)
        self.frm.append(v)
        self.to.append(u)
        self.cap.append(0)
        self.cost.append(-cost)
        self.initial_cap.append(0)
        return eid

    def min_cost_max_flow(
        self, s: int, t: int, flow_limit: int | None = None
    ) -> MinCostFlowResult:
        """Compute an exact minimum-cost flow of maximum possible value.

        If ``flow_limit`` is supplied, maximize flow subject to that upper
        bound and minimize cost among flows of the resulting value.
        """
        if self._solved:
            raise RuntimeError("a MinCostFlow network can be solved only once")
        if not (isinstance(s, int) and isinstance(t, int)):
            raise TypeError("source and sink must be integers")
        if not (0 <= s < self.n and 0 <= t < self.n):
            raise ValueError("source or sink out of range")
        if s == t:
            raise ValueError("source and sink must be distinct")
        if flow_limit is not None and (
            not isinstance(flow_limit, int) or flow_limit < 0
        ):
            raise ValueError("flow_limit must be a nonnegative integer or None")

        self._solved = True
        total_flow = 0
        total_cost = 0
        potential = [0] * self.n

        while flow_limit is None or total_flow < flow_limit:
            dist: list[int | None] = [None] * self.n
            prev = [-1] * self.n
            dist[s] = 0
            heap = [(0, s)]

            while heap:
                du, u = heappop(heap)
                if dist[u] != du:
                    continue
                for eid in self.head[u]:
                    if self.cap[eid] == 0:
                        continue
                    v = self.to[eid]
                    reduced = self.cost[eid] + potential[u] - potential[v]
                    # Forward costs are initially nonnegative.  The potential
                    # invariant makes later negative reverse costs safe here.
                    assert reduced >= 0, (eid, u, v, reduced)
                    nd = du + reduced
                    if dist[v] is None or nd < dist[v]:
                        dist[v] = nd
                        prev[v] = eid
                        heappush(heap, (nd, v))

            if prev[t] < 0:
                break

            for v, dv in enumerate(dist):
                if dv is not None:
                    potential[v] += dv

            amount = flow_limit - total_flow if flow_limit is not None else None
            path_cost = 0
            v = t
            while v != s:
                eid = prev[v]
                assert eid >= 0
                if amount is None or self.cap[eid] < amount:
                    amount = self.cap[eid]
                path_cost += self.cost[eid]
                v = self.frm[eid]
            assert amount is not None and amount > 0

            v = t
            while v != s:
                eid = prev[v]
                self.cap[eid] -= amount
                self.cap[eid ^ 1] += amount
                v = self.frm[eid]

            total_flow += amount
            total_cost += amount * path_cost

        # This also checks cost accounting after augmentations that cancel
        # earlier flow by traversing negative-cost residual reverse edges.
        assert total_cost == sum(
            self.flow_on(eid) * self.cost[eid]
            for eid in range(0, len(self.to), 2)
        )
        return MinCostFlowResult(total_flow, total_cost)

    def flow_on(self, eid: int) -> int:
        """Return the exact final flow on a forward edge id."""
        if not isinstance(eid, int) or eid < 0 or eid >= len(self.to) or eid % 2:
            raise ValueError("eid must identify a forward edge")
        return self.initial_cap[eid] - self.cap[eid]

    def flows(self) -> dict[int, int]:
        """Return all forward-edge flows in deterministic insertion order."""
        return {
            eid: self.flow_on(eid)
            for eid in range(0, len(self.to), 2)
        }
