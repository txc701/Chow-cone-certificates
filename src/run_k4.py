"""Branch B driver: k=4 fourth-central-moment analogue experiments.

Usage:  python3 src/run_k4.py
Writes: results/k4_experiments.json

Steps:
  0. verify B4(d) = (d+2)(5d+8)/240 exactly against Eulerian numbers;
  1. sum-zero sanity: sum of w4 over support == 0;
  2. flow feasibility of divergence-w4 on the same support split-DAG;
  3. if feasible: staircase sums, shell sums, peel2 restriction;
  4. record any infeasibility with its min-cut negative ideal.
"""

import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dinic import Dinic
from flows import FlowResult
from k4_weights import support_w4
from support import split_edges
from weights_bitmask import weight_map  # only for masks / structure reuse
from weights_recursive import mask_of_composition

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def eulerian_mu4_check(dmax: int = 25) -> dict:
    """Record exact B4 and compare with (d+2)(5d+8)/240 (holds for d>=3;
    d=1,2 are genuine exceptions — a Branch-B finding)."""
    from k4_weights import b4_720
    exceptions = {}
    for d in range(1, dmax + 1):
        exact = b4_720(d)
        poly = 3 * (d + 2) * (5 * d + 8)
        if exact != poly:
            exceptions[d] = {"exact_720mu4": exact, "poly_720mu4": poly}
    return exceptions


def k4_flow(d: int, edge_filter=None) -> FlowResult:
    """Max-flow decision for divergence w4 on the support split-DAG."""
    sw = support_w4(d)
    comps = sorted(sw)
    index = {c: k for k, c in enumerate(comps)}
    total_supply = sum(v for v in sw.values() if v > 0)
    inf = total_supply + 1
    source, sink = len(comps), len(comps) + 1
    g = Dinic(len(comps) + 2)
    edge_labels = {}
    for c in comps:
        wv = sw[c]
        if wv > 0:
            g.add_edge(source, index[c], wv)
        elif wv < 0:
            g.add_edge(index[c], sink, -wv)
        for i, p, child in split_edges(c):
            if edge_filter is not None and not edge_filter(c, i, p, child):
                continue
            eid = g.add_edge(index[c], index[child], inf)
            edge_labels[eid] = (c, i, p)
    value = g.max_flow(source, sink)
    return FlowResult(total_supply, value, g, source, sink,
                      {"comps": comps, "index": index, "weights": sw,
                       "edge_labels": edge_labels, "d": d})


def shell_of(c, d):
    j = 0
    for p in c[:-1]:
        j += p
        if j % 2 == 1:
            return j if j <= 2 * (d // 2) - 1 else "residual"
    return "residual"


def main() -> None:
    out = {}
    exc = eulerian_mu4_check()
    print(f"0. B4 polynomial formula exceptions (expected {{1,2}}): {sorted(exc)}")
    out["B4_polynomial_exceptions"] = {str(k): v for k, v in exc.items()}
    assert sorted(exc) == [1, 2]

    rows = []
    first_infeasible = None
    for d in range(1, 21):
        sw = support_w4(d)
        assert sum(sw.values()) == 0, f"sum w4 != 0 at d={d}"
        t0 = time.perf_counter()
        res = k4_flow(d)
        dt = time.perf_counter() - t0
        row = {"d": d, "n_support": len(sw),
               "total_supply": res.total_supply,
               "max_flow": res.max_flow,
               "feasible": res.feasible,
               "deficit": res.deficit,
               "wall_time_sec": round(dt, 3)}
        if not res.feasible and first_infeasible is None:
            first_infeasible = d
            # extract the negative ideal from the min cut
            g = res.dinic
            side = g.min_cut_source_side(res.source)
            comps, index = res.meta["comps"], res.meta["index"]
            ideal = [c for c in comps if not side[index[c]]]
            ideal_sum = sum(sw[c] for c in ideal)
            assert ideal_sum == -res.deficit
            row["negative_ideal"] = [list(c) for c in ideal]
            row["negative_ideal_sum"] = ideal_sum
        rows.append(row)
        status = "FEASIBLE" if res.feasible else f"INFEASIBLE deficit={res.deficit}"
        print(f"2. d={d}: {status} ({dt:.2f}s)")
    out["flow_rows"] = rows
    out["first_infeasible_d"] = first_infeasible

    if first_infeasible is None:
        # structural probes (only meaningful if feasible)
        stair, shells, peel2 = {}, {}, {}
        for d in range(2, 19):
            sw = support_w4(d)
            # staircase sums sigma4(T_k)
            vals = []
            for k in range(d // 2 + 1):
                allowed = set(range(2, 2 * k + 1, 2)) | set(range(2 * k + 1, d + 1))
                s = 0
                for c, wv in sw.items():
                    mask = mask_of_composition(c)
                    if all((mask >> (e - 1)) & 1 == 0 or e in allowed
                           for e in range(1, d + 1)):
                        s += wv
                vals.append(s)
            stair[d] = vals
            sh = {}
            for c, wv in sw.items():
                key = str(shell_of(c, d))
                sh[key] = sh.get(key, 0) + wv
            shells[d] = sh
        for d in range(2, 17):
            res = k4_flow(d, edge_filter=lambda c, i, p, ch:
                          p == 2 or c[i] - p == 2)
            peel2[d] = {"feasible": res.feasible, "deficit": res.deficit}
            print(f"3. peel2 d={d}: feasible={res.feasible}")
        out["staircase_sums"] = {str(k): v for k, v in stair.items()}
        out["shell_sums"] = {str(k): v for k, v in shells.items()}
        out["peel2"] = {str(k): v for k, v in peel2.items()}
        print("3. staircase sums (d=2..8):",
              {k: v for k, v in list(stair.items())[:7]})
        print("3. shell sums nonzero?",
              {d: {k: v for k, v in sh.items() if v != 0}
               for d, sh in list(shells.items())[:7]})

    with open(os.path.join(RESULTS, "k4_experiments.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("wrote results/k4_experiments.json")


if __name__ == "__main__":
    main()
