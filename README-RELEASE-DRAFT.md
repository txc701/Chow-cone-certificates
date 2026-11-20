# Chow cone flows: Cheng–Lin Conjecture 3.30 and the fourth-moment inequality

**Draft README for the public release. Prepared 2026-11-19, revised 2026-11-20, from the
local repository's branch `manuscript-language-pass` (commit `34317b9` before the history
filter described below) plus the new branch `functional-scan`. Items marked TODO must be
settled by the author before publication. Nothing has been published.**

## What this repository contains

Target paper: R. Cheng and W. Lin, *Inequalities for Chow polynomials and Chern numbers of
matroids*, arXiv:2603.21680v3 (the pinned PDF's first page reads `arXiv:2603.21680v3`, confirmed
2026-11-19; arXiv serves v3). Conjecture 3.30 of that paper asserts that the flag inequality
$\sum_{J\subseteq[d]} a_J N_J \le 0$ is a nonnegative linear combination of the monotonicity
inequalities $N_J/U_J \le N_{J'}/U_{J'}$ ($J\subseteq J'$) of their Lemma 3.29, for every
$d\ge 1$. The authors reported computer verification for $d\le 19$.

This repository contains three things, with different levels of verification:

1. **A proof of Conjecture 3.30 for every $d\ge1$** (`PROOF_CONJECTURE_3_30.md`), by an
   explicit uniform certificate: flow $f = G(\text{child})$ on "peel-2" cover edges, where
   $G(c) = U_c\prod_i (n_i-1)$. Its combinatorial core is **machine-checked in Lean 4**
   (`lean/`, Mathlib `v4.32.2`): the divergence identity, flow nonnegativity, the ratio
   lemmas, the in-edge classification, and the summation-by-parts conclusion
   `ChowCone.conjecture_3_30_certificate`. Cheng–Lin's Lemma 3.29 enters only as an explicit
   hypothesis; no matroid or Chow-ring theory is formalized. The correspondence between the
   Lean declarations and the prose proof is tabulated in `LEAN_CORRESPONDENCE.md`.
2. **A proof of the $k=4$ case of Cheng–Lin Conjecture 3.14** (`PROOF_K4_FOURTH_MOMENT.md`,
   `K4_MATROID_BRIDGE.md`): the fourth central moment of the Chow-polynomial distribution of a
   loopless matroid of rank $d+1$ is at most that of the Boolean matroid, via a uniform
   peel-width-three flow certificate. **This part is a symbolic prose proof with exact-integer
   corroboration; it is not formalized in Lean and has not had external human review.**
3. **The exact computations** behind both results (`src/`, `results/`, `tests/`): two
   independent exact-integer implementations of the weights, big-integer max-flow for
   $d\le 25$ (reproducing the authors' $d\le19$ and extending it), the audit of the explicit
   certificate at every node for $d\le 25$, the $k=4$ feasibility scans, and the documented
   **failed searches** for the $k=4$ case (edge-restricted families that die at specific $d$,
   the degree-4 mirror ansatz, the desymmetrized gates; see `K4_*.md`). Everything uses exact
   arithmetic.

4. **An exact finite verification for all even moments** (branch `functional-scan`:
   `FUNCTIONAL_SCAN.md`, `src/functional_scan.py`, `results/functional_scan/`): for
   $1\le d\le 20$ a monotonicity certificate exists for a finite family of generators whose
   nonnegative combinations include every even central moment. Hence Conjecture 3.14 holds
   for every $k$ in ranks 2 to 21, conditional on Cheng–Lin's flag expansion and Lemma 3.29.
   The same computation shows that the absolute deviation has **no** such certificate for
   $4\le d\le 20$; this is a limit of the method, not a matroid counterexample.

The manuscript `CHOW_CONE_FLOWS_MANUSCRIPT.tex` writes up 1 and 2, and on `functional-scan`
also 4.

## Verification status

Details and dates are in `RELEASE_CHECKS.md`.

| item | check | result |
|---|---|---|
| Lean project `lean/`, six modules | compiled from source on 2026-11-19 with `leanprover/lean4:v4.32.2`; Mathlib `v4.32.2` reused from cache | builds; 7 linter warnings, no error |
| nine load-bearing theorems incl. `ChowCone.conjecture_3_30_certificate` | `lake env lean AxiomCheck.lean` | each depends only on `propext`, `Classical.choice`, `Quot.sound` |
| `lean/ChowCone*` | grep for `sorry`, `axiom`, `native_decide`, `skipKernelTC` | none |
| full Python suite incl. all $k=4$ tests | `python3 -m pytest tests/` on 2026-11-20 | 393 passed, 1 failed (hygiene test, see below) |
| functional scan | `src/verify_functional_scan.py` | 153 flows, 22 cuts, 120 brute-force verdicts, 0 problems |
| $k=4$ proof | independent audit of the certificate and of the flag-to-matroid step, 2026-11-20 | no substantive gap found; not formalized, no human referee yet |

The one failing test is `test_no_floating_point_in_sources`: it rejects every `/` token in
`src/`, and `src/k4_weights.py:63` divides exact `Fraction` objects. No floating point is
involved, but the claim "a test statically rejects floating point in `src/`" holds only on
`main` until the test or that line is changed.

The Lean statement of the final theorem is exactly:

```lean
theorem conjecture_3_30_certificate (hn : 3 ≤ n)
    (N U : Composition n → ℚ) (hU : ∀ v, U v ≠ 0)
    (hmono : ∀ q c : Composition n, fEdge q c ≠ 0 → N q / U q ≤ N c / U c) :
    (∑ v : Composition n, (w v.blocks / U v) * N v
      = ∑ v : Composition n, ∑ u : Composition n,
          fEdge v u * (N v / U v - N u / U u))
    ∧ ∑ v : Composition n, (w v.blocks / U v) * N v ≤ 0
```

Here `n = d + 2`, `w` is Cheng–Lin's $U_J a_J$ (proved equal in `w_eq_U_mul_a`), and
`hmono` is Lemma 3.29 restricted to the edges carrying flow. The theorem does not prove
Lemma 3.29 and does not mention matroids.

## What remains unproved or unreviewed

* The $k=4$ theorem (item 2) has no Lean formalization and no external human review.
* Conjecture 3.14 of Cheng–Lin for $k \ne 2, 4$ is untouched. The "peel-width conjecture" in
  `K4_NOTES.md` is a conjecture, supported only by finite computation.
* The exact characterization of tight principal ideals as staircases is empirical
  ($d\le 14$) and is not used by any proof.
* Lemma 3.29 of Cheng–Lin is used as a hypothesis throughout; nothing here re-proves it.

## Reproduce

```sh
# exact-arithmetic computations (Python >= 3.10, stdlib + pytest)
python3 -m pip install pytest
python3 -m pytest tests/ -v                      # full suite; the k4 tests are slow
python3 src/run_stage1_oracle.py                 # reproduces results/stage1_oracle_d1-5.json
python3 src/run_audit_explicit.py                # audit of the explicit k=2 certificate, d <= 25
python3 src/run_functional_scan.py               # branch functional-scan: all even moments, 1 <= d <= 20 (~40 s)
python3 src/verify_functional_scan.py            # independent check of the saved flows and cuts

# Lean certification of the k=2 core (needs elan; downloads Mathlib oleans, ~7 GB)
cd lean
lake exe cache get
lake build
lake env lean AxiomCheck.lean                    # expect only propext, Classical.choice, Quot.sound

# manuscript
latexmk -pdf CHOW_CONE_FLOWS_MANUSCRIPT.tex
```

## Provenance and credit

* Research, code, Lean development and manuscript: Xichen Tang (GitHub `txc701`), August–September 2026.
  The work was done with AI coding assistants (Claude Code; several commits carry
  `Co-Authored-By: Claude` trailers), which is disclosed here.
* The provenance of the explicit $k=2$ certificate formula (Cheng–Lin's coefficients, this
  repository's peel-2 experiments, a candidate proposed by ChatGPT in conversation with the
  author, then audit, proof and Lean certification here) is recorded in `PROVENANCE.md`,
  confirmed by the author on 2026-11-20.
* The manuscript's `\author{Anonymous}` should become the author's name before release
  (**TODO 2**).
* A blind Rethlas verification run (kept in a separate local directory, verdict "correct",
  informal LLM review, not a proof assistant) checked the $k=2$ proof text; it can be cited as
  an informal check only.
* Cheng–Lin's paper is cited, not redistributed: the PDF `paper/cheng-lin-v3.pdf` present in
  the private repository was removed from this release's history (**see "History filter"**).

## History filter

This release clone was produced from the private repository by removing the single blob
`paper/cheng-lin-v3.pdf` (a third-party arXiv PDF) from every commit with
`git filter-branch --index-filter 'git rm --cached --ignore-unmatch paper/cheng-lin-v3.pdf'`.
Commit authorship, dates and messages are otherwise unchanged; commit hashes differ from the
private repository. Mapping of the branch heads: see `RELEASE_CHECKS.md`.

## TODO before publishing

1. Done 2026-11-20: `PROVENANCE.md` confirmed by the author.
2. Replace `\author{Anonymous}` in the manuscript.
3. Add a `LICENSE` file (none exists). Suggested: Apache-2.0 or MIT for `src/`, `tests/`,
   `lean/`; CC BY 4.0 for the Markdown notes and the manuscript, or "all rights reserved" for
   the manuscript if it is to be submitted to a journal.
4. Check whether Cheng–Lin have posted a version after v3 or a published version, and
   whether Conjecture 3.30 or the $k=4$ case of Conjecture 3.14 has been settled elsewhere
   since August 2026, before claiming novelty.
5. The tip commit `34317b9` carries a placeholder text in place of the author e-mail
   (in translation: "your GitHub verified e-mail"). All other commits use machine-local
   addresses that GitHub cannot link to `txc701`. Decide whether to amend the tip
   commit's e-mail (one `git commit --amend --reset-author` on this clone's tip only) and set
   `git config user.email` to a verified address going forward. Do not rewrite older history.
6. Decide which branches to publish. Recommendation: `main` (frozen $k=2$ proof + Lean, head
   `65e1056` in the private repo), and `manuscript-language-pass` (everything incl. $k=4$ and
   the manuscript). `k4-fourth-moment` is an ancestor of `manuscript-language-pass` and
   `external-referee-dc87a7b` is a referee snapshot; both can be published as branches or
   omitted. Note `main` contains the hygiene commit `65e1056` (`lean/AxiomCheck.txt`,
   corrected `STATUS.md`) which is **not** in `manuscript-language-pass`; consider merging
   `main` into it first.
