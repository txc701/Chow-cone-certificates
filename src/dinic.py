"""Dinic max-flow with exact Python-int (arbitrary precision) capacities.

No floating point anywhere.  Compact parallel arrays (no per-edge objects).
"""


class Dinic:
    def __init__(self, n: int):
        self.n = n
        self.head: list[list[int]] = [[] for _ in range(n)]  # edge ids per node
        self.to: list[int] = []
        self.cap: list[int] = []  # residual capacity, exact int

    def add_edge(self, u: int, v: int, cap: int) -> int:
        """Directed edge u->v with capacity cap. Returns edge id (even);
        id^1 is the reverse edge."""
        assert cap >= 0 and isinstance(cap, int)
        eid = len(self.to)
        self.head[u].append(eid)
        self.to.append(v)
        self.cap.append(cap)
        self.head[v].append(eid + 1)
        self.to.append(u)
        self.cap.append(0)
        return eid

    def _bfs(self, s: int, t: int) -> bool:
        self.level = [-1] * self.n
        self.level[s] = 0
        queue = [s]
        for u in queue:
            for eid in self.head[u]:
                v = self.to[eid]
                if self.cap[eid] > 0 and self.level[v] < 0:
                    self.level[v] = self.level[u] + 1
                    queue.append(v)
        return self.level[t] >= 0

    def _dfs(self, s: int, t: int) -> int:
        """Iterative blocking-flow DFS; returns augmented amount (one path)."""
        # path of edge ids from s toward t
        path: list[int] = []
        u = s
        while True:
            if u == t:
                bottleneck = min(self.cap[eid] for eid in path)
                for eid in path:
                    self.cap[eid] -= bottleneck
                    self.cap[eid ^ 1] += bottleneck
                return bottleneck
            advanced = False
            it = self.iter[u]
            while it < len(self.head[u]):
                eid = self.head[u][it]
                v = self.to[eid]
                if self.cap[eid] > 0 and self.level[v] == self.level[u] + 1:
                    path.append(eid)
                    u = v
                    advanced = True
                    break
                it += 1
                self.iter[u] = it
            if not advanced:
                self.level[u] = -1  # dead end; prune
                if not path:
                    return 0
                u = self.to[path.pop() ^ 1]
                self.iter[u] += 1
        # unreachable

    def max_flow(self, s: int, t: int) -> int:
        total = 0
        while self._bfs(s, t):
            self.iter = [0] * self.n
            while True:
                pushed = self._dfs(s, t)
                if pushed == 0:
                    break
                total += pushed
        return total

    def min_cut_source_side(self, s: int) -> list[bool]:
        """After max_flow: nodes reachable from s in the residual graph."""
        seen = [False] * self.n
        seen[s] = True
        queue = [s]
        for u in queue:
            for eid in self.head[u]:
                v = self.to[eid]
                if self.cap[eid] > 0 and not seen[v]:
                    seen[v] = True
                    queue.append(v)
        return seen

    def nodes_reaching_sink(self, t: int) -> list[bool]:
        """After max_flow: nodes that can reach t in the residual graph."""
        seen = [False] * self.n
        seen[t] = True
        queue = [t]
        for u in queue:
            for eid in self.head[u]:
                # v reaches u along residual edge v->u iff cap[eid^1] > 0
                v = self.to[eid]
                if self.cap[eid ^ 1] > 0 and not seen[v]:
                    seen[v] = True
                    queue.append(v)
        return seen

    def flow_on(self, eid: int) -> int:
        """Flow currently on forward edge eid (its reverse residual)."""
        return self.cap[eid ^ 1]
