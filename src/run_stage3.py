"""Stage 3 driver.

Usage: python3 src/run_stage3.py
Writes:
  results/stage3_restrictions.json   feasibility of edge-restricted families
  results/stage3_tightcuts.json      Picard-Queyranne tight-ideal structure
  results/certificates/cert_dXX_<heuristic>.json   distinct certificates
Prints a human-readable summary.
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from certificates import (
    HEURISTICS,
    RESTRICTIONS,
    extract_certificate,
    restricted_feasible,
    tight_cut_structure,
)

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")
D_RESTRICT = range(2, 21)
D_CERT = range(4, 13)
D_TIGHT = range(4, 17)


def main() -> None:
    os.makedirs(os.path.join(RESULTS, "certificates"), exist_ok=True)

    # --- restricted families -------------------------------------------------
    restr_rows = {}
    print("== edge-restricted feasibility ==")
    for name in RESTRICTIONS:
        row = {}
        for d in D_RESTRICT:
            feas, deficit = restricted_feasible(d, name)
            row[d] = {"feasible": feas, "deficit": deficit}
            if not feas and d <= 6:
                pass  # small-d failures are recorded, that's enough
        first_fail = next(
            (d for d in D_RESTRICT if not row[d]["feasible"]), None
        )
        restr_rows[name] = {
            "per_d": {str(d): row[d] for d in D_RESTRICT},
            "first_infeasible_d": first_fail,
            "feasible_for_all_tested": first_fail is None,
        }
        verdict = (
            "SURVIVES all tested d"
            if first_fail is None
            else f"fails first at d={first_fail}"
        )
        print(f"  {name:16s} {verdict}")
    with open(os.path.join(RESULTS, "stage3_restrictions.json"), "w") as f:
        json.dump({"d_range": [min(D_RESTRICT), max(D_RESTRICT)],
                   "families": restr_rows}, f, indent=2)

    # --- structurally distinct certificates ----------------------------------
    print("== certificates by heuristic (support sizes) ==")
    for d in D_CERT:
        sigs = {}
        for h in HEURISTICS:
            t0 = time.perf_counter()
            res, fe = extract_certificate(d, h)
            dt = time.perf_counter() - t0
            sigs[h] = frozenset((c, i, p) for (c, i, p, _) in fe)
            with open(
                os.path.join(RESULTS, "certificates", f"cert_d{d:02d}_{h}.json"),
                "w",
            ) as f:
                json.dump(
                    {
                        "d": d,
                        "heuristic": h,
                        "n_flow_edges": len(fe),
                        "wall_time_sec": round(dt, 3),
                        "edges": [
                            {"comp": list(c), "i": i, "p": p, "flow": fl}
                            for (c, i, p, fl) in sorted(fe)
                        ],
                    },
                    f,
                    indent=2,
                )
        supports = {h: len(s) for h, s in sigs.items()}
        n_distinct = len(set(sigs.values()))
        print(f"  d={d}: support sizes {supports}, distinct supports: {n_distinct}")

    # --- tight cuts -----------------------------------------------------------
    print("== tight-ideal structure (Picard-Queyranne) ==")
    tight_rows = []
    for d in D_TIGHT:
        row = tight_cut_structure(d)
        tight_rows.append(row)
        print(
            f"  d={d}: SCCs={row['n_residual_sccs']} "
            f"min_tight={row['minimal_tight_ideal']['size']} "
            f"max_tight={row['maximal_tight_ideal']['size']} "
            f"nontrivial_samples={row['n_nontrivial_samples']}"
        )
        assert row["minimal_tight_ideal"]["weight_sum"] == 0
        assert row["maximal_tight_ideal"]["weight_sum"] == 0
        for s in row["nontrivial_tight_ideal_samples"]:
            assert s["weight_sum"] == 0
    with open(os.path.join(RESULTS, "stage3_tightcuts.json"), "w") as f:
        json.dump(tight_rows, f, indent=2)


if __name__ == "__main__":
    main()
