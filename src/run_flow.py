"""Stage 2 runner: exact max-flow feasibility test for one dimension d.

Usage:  python3 src/run_flow.py D

Builds the reduced support DAG (RESEARCH_NOTES.md Prop. 3), runs exact
big-integer Dinic, and writes results/flow_dXX.json with the decision,
wall times and peak RSS.  If INFEASIBLE, also writes
results/counterexample_dXX.json containing the deficit, the min-cut and the
corresponding negative-weight downward-closed ideal — that would be the
primary result.

Run each d in a fresh process so peak RSS is per-d.
"""

import json
import os
import resource
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flows import support_flow
from weights_recursive import mask_of_composition

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def main(d: int) -> int:
    t0 = time.perf_counter()
    res = support_flow(d)
    t_total = time.perf_counter() - t0

    meta = res.meta
    sw = meta["weights"]
    n_pos = sum(1 for v in sw.values() if v[2] > 0)
    n_neg = sum(1 for v in sw.values() if v[2] < 0)
    sum_w = sum(v[2] for v in sw.values())
    assert sum_w == 0, f"sum of support weights != 0 at d={d}: {sum_w}"
    max_abs_w = max((abs(v[2]) for v in sw.values()), default=0)

    peak_rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss  # bytes on macOS

    row = {
        "d": d,
        "n_support_nodes": len(sw),
        "n_positive": n_pos,
        "n_negative": n_neg,
        "n_zero_in_support": len(sw) - n_pos - n_neg,
        "n_split_edges": len(meta["edge_labels"]),
        "total_supply": res.total_supply,
        "max_flow": res.max_flow,
        "feasible": res.feasible,
        "deficit": res.deficit,
        "sum_w_support": sum_w,
        "max_abs_w_bits": max_abs_w.bit_length(),
        "wall_time_sec": round(t_total, 3),
        "peak_rss_bytes": peak_rss,
        "python": sys.version.split()[0],
    }
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, f"flow_d{d:02d}.json"), "w") as f:
        json.dump(row, f, indent=2)

    status = "FEASIBLE" if res.feasible else "INFEASIBLE"
    print(
        f"d={d}: {status} nodes={len(sw)} edges={row['n_split_edges']} "
        f"S_bits={res.total_supply.bit_length()} "
        f"time={t_total:.2f}s rss={peak_rss >> 20}MiB"
    )

    if not res.feasible:
        # Min cut -> negative ideal (RESEARCH_NOTES.md Sec. 3.4):
        # source side C of the min cut is upward-closed in the support poset;
        # the complement D is a down-closed ideal with sum_D w = -deficit.
        g = res.dinic
        side = g.min_cut_source_side(res.source)
        comps = meta["comps"]
        index = meta["index"]
        ideal = [c for c in comps if not side[index[c]]]
        ideal_sum = sum(sw[c][2] for c in ideal)
        assert ideal_sum == -res.deficit, (ideal_sum, res.deficit)
        cut_source_edges = [
            list(c) for c in comps if side[index[c]] and sw[c][2] < 0
        ]  # negative nodes on source side (their sink edges are cut)
        cut_supply_edges = [
            list(c) for c in comps if not side[index[c]] and sw[c][2] > 0
        ]  # positive nodes on sink side (their source edges are cut)
        with open(os.path.join(RESULTS, f"counterexample_d{d:02d}.json"), "w") as f:
            json.dump(
                {
                    "d": d,
                    "deficit": res.deficit,
                    "ideal_weight_sum": ideal_sum,
                    "ideal_compositions": [list(c) for c in ideal],
                    "ideal_masks": [mask_of_composition(c) for c in ideal],
                    "min_cut": {
                        "cut_sink_edges_at": cut_source_edges,
                        "cut_source_edges_at": cut_supply_edges,
                    },
                    "note": (
                        "Downward-closed ideal of the support poset; its "
                        "downward closure in 2^[d] adds only zero-weight "
                        "nodes. Negative sum refutes Conjecture 3.30 for "
                        "this d (see RESEARCH_NOTES.md Prop. 2/3)."
                    ),
                },
                f,
                indent=2,
            )
        print(f"  COUNTEREXAMPLE written: ideal of {len(ideal)} support nodes, "
              f"weight sum {ideal_sum}")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1])))
