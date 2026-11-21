"""Driver for the functional scan.

Usage:  python3 src/run_functional_scan.py [DMAX] [DWIDTH] [DFLOW] [--witnesses FILE]
        (defaults 20 16 10)
Writes: results/functional_scan/summary.json   verdicts for 1 <= d <= DMAX
        results/functional_scan/cuts.json      an infeasibility certificate
                                               for every infeasible case
        results/functional_scan/flows.json     a flow certificate for every
                                               feasible case with d <= DFLOW
With --witnesses FILE it also writes one compact witness per case for the tail
generators and the absolute deviation, 1 <= d <= DMAX (gzip, one JSON object per
line; format described in functional_scan.py).  For DMAX = 20 these are the 100
instances of the finite verification plus 20 absolute-deviation cases.
Output is deterministic, byte for byte.  Check it with
src/verify_functional_scan.py [--witnesses FILE].
"""

import gzip
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional_scan import (Level, check_witness, exp_phi,  # noqa: E402
                             make_witness, moment_phi, shell_phi, shell_values,
                             tail_decomposition, tail_phi, witness_cases)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results",
                   "functional_scan")
MOMENTS = (2, 4, 6, 8, 10, 12, 16, 24)
WIDTH_MOMENTS = MOMENTS + (40,)
EXP_BASES = (2, 3, 10)


def functionals(d: int):
    for k in MOMENTS:
        yield "moment_%d" % k, moment_phi(d, k)
    for m in shell_values(d):
        yield "tail_%d" % m, tail_phi(d, m)
    for m in shell_values(d):
        yield "shell_%d" % m, shell_phi(d, m)
    for x in EXP_BASES:
        yield "exp_%d" % x, exp_phi(d, x)


def main() -> None:
    args = sys.argv[1:]
    witness_path = None
    if "--witnesses" in args:
        k = args.index("--witnesses")
        witness_path = args[k + 1]
        del args[k:k + 2]
    dmax = int(args[0]) if len(args) > 0 else 20
    dwidth = int(args[1]) if len(args) > 1 else 16
    dflow = int(args[2]) if len(args) > 2 else 10
    os.makedirs(OUT, exist_ok=True)
    witness_lines = []
    summary = {"d_range": [1, dmax], "width_d_range": [1, dwidth],
               "flow_d_range": [1, dflow], "moments": list(MOMENTS),
               "levels": {}, "min_peel_width": {}}
    cuts, flows = {}, {}
    for d in range(1, dmax + 1):
        level = Level(d)
        assert level.boolean_identity_holds()
        row = {"nodes": len(level.comps), "feasible": [], "infeasible": {}}
        for name, phi in functionals(d):
            w = level.weights(phi)
            assert sum(w.values()) == 0
            res = level.solve(w, want="certificate")
            if res["feasible"]:
                row["feasible"].append(name)
                if d <= dflow:
                    flows["%d:%s" % (d, name)] = {"scale": res["scale"], "flow": res["flow"]}
            else:
                row["infeasible"][name] = {
                    "deficit": res["total_supply"] - res["max_flow"],
                    "total_supply": res["total_supply"], "scale": res["scale"]}
                cuts["%d:%s" % (d, name)] = res["cut_generators"]
        # every even moment decomposes over the tail generators
        row["tail_decomposition_ok"] = all(
            tail_decomposition(moment_phi(d, k)) is not None for k in range(2, 42, 2))
        summary["levels"][str(d)] = row
        if witness_path is not None:
            for dd, kind, m in witness_cases(d):
                if dd == d:
                    rec = make_witness(level, kind, m)
                    assert check_witness(level, rec) == ""
                    witness_lines.append(json.dumps(rec, separators=(",", ":"), sort_keys=True))
        print("d=%2d nodes=%6d infeasible=%s" % (d, len(level.comps),
                                                 sorted(row["infeasible"])), flush=True)
    for k in WIDTH_MOMENTS:
        need = {}
        for d in range(1, dwidth + 1):
            level = Level(d)
            w = level.weights(moment_phi(d, k))
            t = 2
            while not level.solve(w, width=t)["feasible"]:
                t += 1
            need[str(d)] = t
        summary["min_peel_width"]["moment_%d" % k] = need
        print("k=%2d min peel width by d: %s" % (k, list(need.values())), flush=True)
    for name, obj in (("summary.json", summary), ("cuts.json", cuts), ("flows.json", flows)):
        with open(os.path.join(OUT, name), "w") as f:
            json.dump(obj, f, indent=1, sort_keys=True)
            f.write("\n")
    if witness_path is not None:
        # fixed mtime and empty embedded name: the archive is reproducible byte for byte
        with open(witness_path, "wb") as raw:
            with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0,
                               compresslevel=6) as gz:
                for line in witness_lines:
                    gz.write((line + "\n").encode("ascii"))
        print("wrote %d witnesses to %s" % (len(witness_lines), witness_path))


if __name__ == "__main__":
    main()
