"""Regenerate and PERSIST the peel2 edge-restriction feasibility for
d = 21..25 (transcript-only after the 2026-08-11 session interruption).

Usage:  python3 src/run_peel2_ext.py
Writes: results/stage3_peel2_d21-25.json
"""

import json
import os
import resource
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from certificates import restricted_feasible

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def main() -> None:
    rows = []
    for d in range(21, 26):
        t0 = time.perf_counter()
        feas, deficit = restricted_feasible(d, "peel2")
        dt = time.perf_counter() - t0
        rows.append(
            {
                "d": d,
                "restriction": "peel2",
                "feasible": feas,
                "deficit": deficit,
                "wall_time_sec": round(dt, 3),
                "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            }
        )
        print(f"peel2 d={d}: feasible={feas} deficit={deficit} ({dt:.1f}s)",
              flush=True)
        if not feas:
            print("peel2 hypothesis KILLED at this d", flush=True)
            break
    with open(os.path.join(RESULTS, "stage3_peel2_d21-25.json"), "w") as f:
        json.dump(rows, f, indent=2)


if __name__ == "__main__":
    main()
