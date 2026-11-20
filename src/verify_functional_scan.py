"""Independent check of results/functional_scan/*.json.

Uses no max-flow code for the saved certificates:
  * every saved flow is re-checked edge by edge (legal split, positive amount,
    divergence equal to the weight);
  * every saved cut is re-checked (ancestor-closed set with negative weight);
  * for d <= DBRUTE (default 8) every verdict is compared with a brute-force
    minimum over all ancestor-closed sets.
Exits with status 1 on any disagreement.

Usage:  python3 src/verify_functional_scan.py [DBRUTE]
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional_scan import (Level, check_cut, check_flow, exp_phi,  # noqa: E402
                             min_ideal_sum, moment_phi, shell_phi, tail_phi)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results",
                   "functional_scan")


def phi_of(d: int, name: str) -> list[int]:
    kind, arg = name.split("_")
    return {"moment": moment_phi, "tail": tail_phi, "shell": shell_phi,
            "exp": exp_phi}[kind](d, int(arg))


def main() -> int:
    dbrute = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    load = lambda n: json.load(open(os.path.join(OUT, n)))  # noqa: E731
    summary, cuts, flows = load("summary.json"), load("cuts.json"), load("flows.json")
    bad = 0
    levels = {}

    def level(d: int) -> Level:
        if d not in levels:
            levels[d] = Level(d)
        return levels[d]

    for key, rec in sorted(flows.items()):
        d, name = key.split(":")
        lv = level(int(d))
        if not check_flow(lv, lv.weights(phi_of(int(d), name)), rec["scale"], rec["flow"]):
            print("BAD FLOW", key)
            bad += 1
    for key, gens in sorted(cuts.items()):
        d, name = key.split(":")
        lv = level(int(d))
        if not check_cut(lv, lv.weights(phi_of(int(d), name)), gens):
            print("BAD CUT", key)
            bad += 1
    n_brute = 0
    for d in range(1, min(dbrute, summary["d_range"][1]) + 1):
        lv = level(d)
        row = summary["levels"][str(d)]
        for name in row["feasible"] + sorted(row["infeasible"]):
            mn, _ = min_ideal_sum(lv, lv.weights(phi_of(d, name)))
            n_brute += 1
            if (mn >= 0) != (name in row["feasible"]):
                print("BRUTE-FORCE DISAGREEMENT", d, name, mn)
                bad += 1
    n_inf = sum(len(r["infeasible"]) for r in summary["levels"].values())
    if n_inf != len(cuts):
        print("MISSING CUT CERTIFICATES", n_inf, len(cuts))
        bad += 1
    print("flows checked: %d   cuts checked: %d   brute-force verdicts: %d   problems: %d"
          % (len(flows), len(cuts), n_brute, bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
