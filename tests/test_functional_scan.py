"""Tests for src/functional_scan.py (exact arithmetic; small d, fast)."""
import json
import os
import subprocess
import sys

import pytest

import functional_scan as fs
from k4_weights import w4_value

ROOT = os.path.join(os.path.dirname(__file__), "..")
RES = os.path.join(ROOT, "results", "functional_scan")


@pytest.mark.parametrize("d", range(1, 13))
def test_boolean_matroid_reproduces_eulerian_numbers(d):
    assert fs.Level(d).boolean_identity_holds()


@pytest.mark.parametrize("d", range(1, 13))
def test_every_flag_distribution_and_the_eulerian_one_have_mean_d_over_2(d):
    lv = fs.Level(d)
    for c in lv.comps:
        cnt = lv.cnt[c]
        assert sum(cnt) == lv.prod[c]
        assert 2 * sum(p * x for p, x in enumerate(cnt)) == d * sum(cnt)
    assert 2 * sum(p * a for p, a in enumerate(lv.eulerian)) == d * sum(lv.eulerian)


@pytest.mark.parametrize("d", range(1, 11))
def test_affine_functions_have_zero_weight_so_weights_are_affine_invariant(d):
    lv = fs.Level(d)
    for alpha, beta in ((1, 0), (0, 1), (-7, 3)):
        w = lv.weights([alpha + beta * p for p in range(d + 1)])
        assert all(v == 0 for v in w.values())
    # consequence: a generator and its mirror image give the same weight,
    # and phi + mirror(phi) (which IS symmetric) gives twice that weight
    for m in fs.shell_values(d):
        for fam in (fs.tail_phi, fs.shell_phi):
            phi = fam(d, m)
            mirror = phi[::-1]
            assert fs.is_affine([x - y for x, y in zip(phi, mirror)])
            w, wm = lv.weights(phi), lv.weights(mirror)
            ws = lv.weights([x + y for x, y in zip(phi, mirror)])
            assert w == wm and all(ws[c] == 2 * w[c] for c in lv.comps)


def test_central_shell_is_the_absolute_deviation():
    # the example from review: shell_phi(4, 0) = (p-2)_+ and 2(p-2)_+ = |p-2| + (p-2)
    assert fs.shell_phi(4, 0) == [0, 0, 0, 1, 2]
    for d in range(2, 13):
        m = d % 2
        phi = fs.shell_phi(d, m)
        target = [abs(2 * p - d) for p in range(d + 1)]
        c = 2 if d % 2 == 0 else 1    # |2p-d| has second difference 4 (even d) or 2 (odd d)
        assert fs.is_affine([2 * c * x - y for x, y in zip(phi, target)])


@pytest.mark.parametrize("d", range(1, 13))
def test_weights_agree_with_the_k2_and_k4_weights_of_the_repository(d):
    lv = fs.Level(d)
    w4 = lv.weights(fs.moment_phi(d, 4))
    w2 = lv.weights(fs.moment_phi(d, 2))
    for c in lv.comps:
        assert w4[c] * 45 == lv.fact * w4_value(c, d)
        assert w2[c] * 3 == lv.fact * lv.U[c] * lv.prod[c] * sum(m * (m - 3) for m in c)


@pytest.mark.parametrize("d", range(1, 21))
def test_even_moments_decompose_nonnegatively_over_the_tail_generators(d):
    for k in range(2, 42, 2):
        phi = fs.moment_phi(d, k)
        lam = fs.second_difference(phi)
        for a in range(1, d):
            assert lam[a] == fs.moment_second_difference(d, k, a) >= 0
        mu = fs.tail_decomposition(phi)      # verifies phi = sum mu_m tail_m + affine exactly
        assert mu is not None and all(v >= 0 for v in mu.values())
    # the decomposition transfers to weights
    if d <= 10:
        lv = fs.Level(d)
        mu = fs.tail_decomposition(fs.moment_phi(d, 6))
        combo = {c: 0 for c in lv.comps}
        for m, coef in mu.items():
            wt = lv.weights(fs.tail_phi(d, m))
            for c in lv.comps:
                combo[c] += coef * wt[c]
        assert combo == lv.weights(fs.moment_phi(d, 6))


def test_functions_outside_the_tail_cone_are_rejected_by_the_decomposition():
    assert fs.tail_decomposition(fs.hinge_phi(8, 3)) is None      # not symmetric
    assert fs.tail_decomposition(fs.shell_phi(8, 0)) is None      # not outward-nondecreasing
    assert fs.tail_decomposition(fs.shell_phi(8, 2)) is None


def test_recorded_k4_peel_thresholds_are_reproduced():
    feasible2 = []
    for d in range(1, 13):
        lv = fs.Level(d)
        w = lv.weights(fs.moment_phi(d, 4))
        assert lv.solve(w)["feasible"] and lv.solve(w, width=3)["feasible"]
        if lv.solve(w, width=2)["feasible"]:
            feasible2.append(d)
    assert feasible2 == [1, 2, 3, 5]          # K4_NOTES.md: peel2 dies at d=4


@pytest.mark.parametrize("d", range(1, 13))
def test_moments_and_tail_family_feasible_with_checked_certificates(d):
    lv = fs.Level(d)
    phis = [fs.moment_phi(d, k) for k in (6, 8, 12, 24)]
    phis += [fs.tail_phi(d, m) for m in fs.shell_values(d)]
    for phi in phis:
        w = lv.weights(phi)
        res = lv.solve(w, want="certificate")
        assert res["feasible"] and fs.check_flow(lv, w, res["scale"], res["flow"])


@pytest.mark.parametrize("d", range(4, 13))
def test_absolute_deviation_has_no_certificate_and_the_cut_proves_it(d):
    lv = fs.Level(d)
    w = lv.weights(fs.shell_phi(d, d % 2))
    res = lv.solve(w, want="certificate")
    assert not res["feasible"] and fs.check_cut(lv, w, res["cut_generators"])


def test_d4_obstruction_by_hand():
    # leaf (3,3) has positive weight and no outgoing support edge
    lv = fs.Level(4)
    w = lv.weights(fs.shell_phi(4, 0))
    scale = lv.solve(w)["scale"]
    assert lv.splits[(3, 3)] == []
    assert {c: v // scale for c, v in w.items()} == {
        (6,): 11, (2, 4): 18, (4, 2): 9, (3, 3): 4, (2, 2, 2): -42}


@pytest.mark.parametrize("d", range(1, 8))
def test_flow_verdicts_agree_with_brute_force_over_all_ancestor_closed_sets(d):
    lv = fs.Level(d)
    phis = [fs.moment_phi(d, k) for k in (2, 4, 6, 8)]
    for m in fs.shell_values(d):
        phis += [fs.tail_phi(d, m), fs.shell_phi(d, m)]
    for phi in phis:
        w = lv.weights(phi)
        assert lv.solve(w)["feasible"] == (fs.min_ideal_sum(lv, w)[0] >= 0)


def test_certificate_checkers_reject_corrupted_certificates():
    lv = fs.Level(6)
    w = lv.weights(fs.moment_phi(6, 6))
    res = lv.solve(w, want="certificate")
    flow = [list(e) for e in res["flow"]]
    flow[0][2] += 1
    assert not fs.check_flow(lv, w, res["scale"], flow)
    w0 = lv.weights(fs.shell_phi(6, 0))
    assert not fs.check_cut(lv, w0, [[8]])            # complement empty: sum 0, not negative
    assert not fs.check_cut(lv, w, lv.solve(w0, want="certificate")["cut_generators"])


def test_saved_results_are_complete_and_pass_the_independent_verifier():
    summary = json.load(open(os.path.join(RES, "summary.json")))
    assert summary["d_range"] == [1, 20]
    for d in range(1, 21):
        row = summary["levels"][str(d)]
        bad = sorted(row["infeasible"])
        assert all(name.startswith("shell_") for name in bad)
        assert row["tail_decomposition_ok"]
        if d >= 4:
            assert "shell_%d" % (d % 2) in bad
    out = subprocess.run([sys.executable, os.path.join(ROOT, "src", "verify_functional_scan.py"), "6"],
                         capture_output=True, text=True)
    assert out.returncode == 0, out.stdout + out.stderr
    assert "problems: 0" in out.stdout
