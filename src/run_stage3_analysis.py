"""Stage 3 structural analysis (reproduces everything in RESEARCH_NOTES.md
Section 8).  Usage:  python3 src/run_stage3_analysis.py
Writes results/stage3_analysis.json.

Findings reproduced here:
  A. staircase characterization of tight principal ideals (exact, d <= 12);
  B. shell identities: per-shell weight sums vanish (d <= 25);
  C. every saved certificate respects the shell decomposition (0 crossings);
  D. failed idea: U-proportional cascades (plain and alive-pruned) break;
  E. rigid skeleton: edges with identical flow across all 4 heuristics.
"""

import json
import os
import sys
from collections import defaultdict
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from support import support_weights, split_edges
from weights_bitmask import weight_map

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def staircase_masks(d: int) -> set[int]:
    """{T_k, T_k u {1}}: T_k = {2,4,...,2k} u {2k+1,...,d}, 0<=k<=d//2."""
    fam = set()
    for k in range(d // 2 + 1):
        mask = 0
        for e in range(2, 2 * k + 1, 2):
            mask |= 1 << (e - 1)
        for e in range(2 * k + 1, d + 1):
            mask |= 1 << (e - 1)
        fam.add(mask)
        fam.add(mask | 1)
    return fam


def tight_principal_ideals_match(d: int) -> bool:
    """sigma(T) = sum_{J<=T} w_J via zeta transform; compare zero set."""
    wm = weight_map(d)
    f = [wm[m][2] for m in range(1 << d)]
    for b in range(d):
        bit = 1 << b
        for m in range(1 << d):
            if m & bit:
                f[m] += f[m ^ bit]
    assert min(f) == 0, f"NEGATIVE principal ideal at d={d}!"
    return {m for m in range(1 << d) if f[m] == 0} == staircase_masks(d)


def shell_of(c: tuple[int, ...], d: int):
    """Smallest odd proper prefix sum, with everything >= 2*(d//2)+1
    (and 'no odd prefix') merged into the residual class."""
    j = 0
    for p in c[:-1]:
        j += p
        if j % 2 == 1:
            return j if j <= 2 * (d // 2) - 1 else "residual"
    return "residual"


def shell_sums_vanish(d: int) -> bool:
    sums = defaultdict(int)
    for c, (_, _, w) in support_weights(d).items():
        sums[shell_of(c, d)] += w
    return all(v == 0 for v in sums.values())


def certificate_shell_crossings() -> tuple[int, int]:
    import glob

    crossing = total = 0
    for path in sorted(glob.glob(os.path.join(RESULTS, "certificates", "*.json"))):
        cert = json.load(open(path))
        d = cert["d"]
        for e in cert["edges"]:
            c = tuple(e["comp"])
            i, p = e["i"], e["p"]
            child = c[:i] + (p, c[i] - p) + c[i + 1 :]
            total += 1
            if shell_of(c, d) != shell_of(child, d):
                crossing += 1
    return total, crossing


def cascade(d: int, pruned: bool):
    """U-proportional forward cascade; returns failure reason or None."""
    sw = support_weights(d)
    comps = sorted(sw, key=len)
    kids_of = {c: [ch for (_, _, ch) in split_edges(c)] for c in comps}
    alive = {}
    for c in sorted(comps, key=len, reverse=True):
        alive[c] = sw[c][2] < 0 or any(alive[ch] for ch in kids_of[c])
    inflow = {c: Fraction(0) for c in comps}
    for c in comps:
        out = inflow[c] + sw[c][2]
        if out < 0:
            return f"negative excess at {c}"
        kids = [ch for ch in kids_of[c] if (alive[ch] if pruned else True)]
        if out == 0:
            continue
        if not kids:
            return f"stranded at {c}"
        tot = sum(sw[ch][0] for ch in kids)
        for ch in kids:
            inflow[ch] += out * Fraction(sw[ch][0], tot)
    return None


def rigid_skeleton():
    rows = {}
    for d in range(4, 13):
        certs = []
        for h in ("early_small", "late_small", "balanced", "unbalanced"):
            j = json.load(
                open(os.path.join(RESULTS, "certificates", f"cert_d{d:02d}_{h}.json"))
            )
            certs.append(
                {(tuple(e["comp"]), e["i"], e["p"]): e["flow"] for e in j["edges"]}
            )
        union = set().union(*certs)
        rows[d] = {
            "union_support": len(union),
            "in_all_four": sum(1 for e in union if all(e in c for c in certs)),
            "identical_flow_in_all_four": sum(
                1 for e in union if len({c.get(e, 0) for c in certs}) == 1
            ),
        }
    return rows


def main() -> None:
    out = {}
    print("A. tight principal ideals == staircase family:")
    out["staircase_exact_match"] = {}
    for d in range(2, 13):
        ok = tight_principal_ideals_match(d)
        out["staircase_exact_match"][str(d)] = ok
        print(f"   d={d}: {ok}")
        assert ok
    print("B. shell identities (per-shell weight sums vanish):")
    out["shell_sums_vanish"] = {}
    for d in range(2, 26):
        ok = shell_sums_vanish(d)
        out["shell_sums_vanish"][str(d)] = ok
        assert ok
    print("   all True for d=2..25")
    total, crossing = certificate_shell_crossings()
    print(f"C. saved certificates: {total} flow edges, {crossing} shell crossings")
    out["certificate_flow_edges_checked"] = total
    out["certificate_shell_crossings"] = crossing
    assert crossing == 0
    print("D. failed cascades (first failure per variant):")
    out["cascade_failures"] = {}
    for pruned in (False, True):
        fails = {}
        for d in range(2, 9):
            reason = cascade(d, pruned)
            if reason:
                fails[str(d)] = reason
        out["cascade_failures"]["pruned" if pruned else "plain"] = fails
        print(f"   {'pruned' if pruned else 'plain '}: {fails}")
    out["rigid_skeleton"] = rigid_skeleton()
    print("E. rigid skeleton:", out["rigid_skeleton"])
    with open(os.path.join(RESULTS, "stage3_analysis.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("wrote results/stage3_analysis.json")


if __name__ == "__main__":
    main()
