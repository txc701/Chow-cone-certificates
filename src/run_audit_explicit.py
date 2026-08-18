"""Audit protocol for the external explicit peel2 certificate.

Usage:  python3 src/run_audit_explicit.py
Writes: results/audit_explicit_certificate.json

Checks (see the audit request; letters match):
  C. the three G-ratio identities, verified exactly for all block sizes
     m = 4..200 embedded in random contexts;
  E/F1. divergence of the explicit certificate == w at EVERY support node,
     for every d = 1..25 (exact integers);
  F2. every explicit edge is a peel2 split edge of the existing network
     (checked structurally for all d, and against the constructed peel2
     network edge set for d <= 12);
  F3. full-Boolean check for d <= 10: divergence == w over ALL 2^d subsets
     (zero off the support);
  F4. positivity: every flow value > 0.
"""

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from explicit_certificate import certificate, divergence, g_value, rho, w_value
from flows import build_support_network
from support import support_compositions
from weights_bitmask import composition_of, uaw_from_composition, weight_map
from weights_recursive import mask_of_composition

RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")


def check_ratios() -> None:
    """C: exact ratio identities in randomized contexts (no floats)."""
    contexts = [((), ()), ((2,), ()), ((5, 2), (3,)), ((2, 3), (4, 2))]
    for m in range(4, 201):
        for left, right in contexts:
            # nonfinal: c = left + (m,) + right + (2,), so m is nonfinal
            c = left + (m,) + right + (2,)
            d = sum(c) - 2
            child = left + (2, m - 2) + right + (2,)
            assert g_value(child, d) == g_value(c, d) * rho(m)
            # final: c2 = left + right + (m,)
            c2 = left + right + (m,)
            d2 = sum(c2) - 2
            child_l = left + right + (2, m - 2)
            child_r = left + right + (m - 2, 2)
            assert 2 * g_value(child_l, d2) == g_value(c2, d2) * (m - 2) * (m - 3)
            assert g_value(child_r, d2) == g_value(c2, d2) * (m - 3)
            assert (2 * g_value(child_l, d2) + 2 * g_value(child_r, d2)
                    == g_value(c2, d2) * 2 * rho(m))
    print("C. ratio identities: exact for m=4..200 in 4 contexts each")


def audit_d(d: int) -> dict:
    t0 = time.perf_counter()
    div = divergence(d)
    bad = []
    for c in div:
        # w from the twice-validated Stage-1 implementation (NOT w_value):
        w_ref = uaw_from_composition(c, d)[2]
        assert w_value(c, d) == w_ref, ("w formula mismatch", c)
        if div[c] != w_ref:
            bad.append((c, div[c], w_ref))
    flows = certificate(d)
    n_pos = sum(1 for f in flows.values() if f > 0)
    assert n_pos == len(flows), "nonpositive flow found"
    # structural peel2 check on every edge
    for (c, i, p), f in flows.items():
        m = c[i]
        assert m >= 4 and (p == 2 or m - p == 2), ("not a peel2 split", c, i, p)
        child = c[:i] + (p, m - p) + c[i + 1 :]
        assert all(x >= 2 for x in child)
    dt = time.perf_counter() - t0
    return {
        "d": d,
        "n_support_nodes": len(div),
        "n_certificate_edges": len(flows),
        "divergence_mismatches": len(bad),
        "wall_time_sec": round(dt, 3),
        "first_mismatch": (
            [list(bad[0][0]), bad[0][1], bad[0][2]] if bad else None
        ),
    }


def check_against_peel2_network(d: int) -> None:
    """F2: explicit edges form a subset of the peel2 network's edges."""
    net = build_support_network(
        d, edge_filter=lambda c, i, p, ch: p == 2 or c[i] - p == 2
    )
    labels = set(net[6].values())  # {(comp, i, p)}
    for key in certificate(d):
        assert key in labels, ("edge not in peel2 network", d, key)


def check_full_boolean(d: int) -> None:
    """F3: divergence over ALL 2^d subsets equals w (0 off support)."""
    wm = weight_map(d)
    div = {m: 0 for m in range(1 << d)}
    for c in support_compositions(d):
        mask = mask_of_composition(c)
        prefix = 0
        for i, p, child, f in [(i, p, ch, f) for (i, p, ch, f) in
                               __import__("explicit_certificate").explicit_edges(c, d)]:
            child_mask = mask_of_composition(child)
            # child adds exactly one element:
            added = child_mask & ~mask
            assert added and (added & (added - 1)) == 0, "not a cover edge"
            div[mask] += f
            div[child_mask] -= f
    for m in range(1 << d):
        assert div[m] == wm[m][2], ("full-lattice divergence mismatch", d, m)


def main() -> None:
    check_ratios()
    rows = []
    ok = True
    for d in range(1, 26):
        row = audit_d(d)
        rows.append(row)
        status = "OK" if row["divergence_mismatches"] == 0 else "MISMATCH"
        print(f"E/F1. d={d}: {status} nodes={row['n_support_nodes']} "
              f"edges={row['n_certificate_edges']} ({row['wall_time_sec']}s)")
        if row["divergence_mismatches"]:
            ok = False
            print("   FIRST MISMATCH:", row["first_mismatch"])
            break
    if ok:
        for d in range(2, 13):
            check_against_peel2_network(d)
        print("F2. explicit edges subset of peel2 network: OK for d=2..12")
        for d in range(1, 11):
            check_full_boolean(d)
        print("F3. full-Boolean divergence == w over all 2^d subsets: OK d<=10")
    with open(os.path.join(RESULTS, "audit_explicit_certificate.json"), "w") as f:
        json.dump({"ratio_identities_m4_200": True, "per_d": rows,
                   "all_passed": ok}, f, indent=2)
    print("VERDICT:", "ALL AUDITS PASSED" if ok else "AUDIT FAILED — see above")


if __name__ == "__main__":
    main()
