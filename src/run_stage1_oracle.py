"""Stage 1 oracle run: for d = 1..5, compare
  (a) brute-force minimum weight-sum over ALL down-closed ideals of 2^[d],
  (b) exact max-flow on the full Boolean-lattice network,
  (c) exact max-flow on the reduced support DAG.
Writes results/stage1_oracle_d1-5.json.

Usage:  python3 src/run_stage1_oracle.py
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flows import full_lattice_flow, support_flow
from ideals import min_ideal_sum


def main() -> None:
    rows = []
    for d in range(1, 6):
        t0 = time.perf_counter()
        best, best_ideal, n_ideals = min_ideal_sum(d)
        t_ideals = time.perf_counter() - t0

        t0 = time.perf_counter()
        lat = full_lattice_flow(d)
        t_lat = time.perf_counter() - t0

        t0 = time.perf_counter()
        sup = support_flow(d)
        t_sup = time.perf_counter() - t0

        agree = (
            lat.total_supply == sup.total_supply
            and lat.max_flow == sup.max_flow
            and lat.deficit == -best
            and sup.deficit == -best
            and lat.feasible == sup.feasible == (best == 0)
        )
        row = {
            "d": d,
            "n_ideals_enumerated": n_ideals,
            "min_ideal_weight_sum": best,
            "a_minimizing_ideal_masks": sorted(best_ideal),
            "total_supply": lat.total_supply,
            "max_flow_full_lattice": lat.max_flow,
            "max_flow_support_dag": sup.max_flow,
            "feasible": sup.feasible,
            "deficit": sup.deficit,
            "oracle_and_flows_agree": agree,
            "wall_time_sec": {
                "ideal_enumeration": round(t_ideals, 6),
                "full_lattice_flow": round(t_lat, 6),
                "support_dag_flow": round(t_sup, 6),
            },
        }
        rows.append(row)
        status = "FEASIBLE" if row["feasible"] else "INFEASIBLE"
        print(
            f"d={d}: ideals={n_ideals}, min_ideal_sum={best}, "
            f"supply={row['total_supply']}, maxflow={row['max_flow_support_dag']}, "
            f"{status}, agree={agree}"
        )
        if not agree:
            print("MISMATCH between oracle and max-flow — investigate!", file=sys.stderr)
            sys.exit(1)

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "stage1_oracle_d1-5.json")
    with open(out, "w") as f:
        json.dump(rows, f, indent=2)
    print(f"wrote {os.path.normpath(out)}")


if __name__ == "__main__":
    main()
