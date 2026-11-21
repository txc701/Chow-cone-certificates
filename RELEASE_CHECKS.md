# Release checks

Records of what was run on the release candidate, when, and with which result. Checks were
run on the author's Mac by an AI assistant (Claude Code) at the author's request. "Old log"
marks anything not run on the stated date. The private repository was never modified.

## History

The public history is the private history with one file, `paper/cheng-lin-v3.pdf`, removed
from every commit. `COMMIT_MAP.md` maps all 26 private commits to their public hashes.

| branch | private head | public head |
|---|---|---|
| `main` | `65e1056` | `520d3a0` |
| `k4-fourth-moment` | `6360104` | `bee8307` |
| `manuscript-language-pass` | `34317b9` | `6845da3` |
| `external-referee-dc87a7b` | `dc87a7b` | `8824621` |

The branch `functional-scan` exists only in the public line. It contains
`manuscript-language-pass`, the two commits that were only on `main`, and the work of
November 2026. `main` is an ancestor of it, so releasing it as `main` is a fast-forward.

`git rev-list --objects --all | grep cheng-lin-v3.pdf` returns nothing.

Correction, 2026-11-21. The first preparation of this history (2026-11-19) used
`git filter-branch --prune-empty`. The project's first commit of 9 August 2026 contained only
the removed PDF, so it became empty and was silently dropped, and the history began on
12 August. That was noticed while building `COMMIT_MAP.md`. The commit has been restored as an
empty commit with its original author, committer, dates and message, and all later commits
were re-parented onto it. Nothing had been published.

## Lean, `k = 2` (2026-11-19)

The first `lake build` of 2026-11-19, run in the private worktree, reported the project
modules as "Replayed". That is a cache hit: Lake confirmed that the stored build products
match the current sources, and `#print axioms` was evaluated against those stored products.
Nothing was recompiled in that run. The check that counts is the second one, run the same
day in the public line:

* `lean/` is byte-identical to the private worktree's `lean/` (`diff -rq`), apart from
  `lean/AxiomCheck.txt`, which exists on `main` and after the merge of 2026-11-21 also here.
* The Mathlib package directory was cloned copy-on-write from the private worktree.
  `lake build --no-build Mathlib` reported "All targets up-to-date (8654 jobs)", so Mathlib
  itself was **reused from cache, not recompiled**.
* `lake build` then compiled the **six project modules** from source, with no prior build
  directory: `ChowCone.Abstract`, `Basic`, `Flow`, `Ratios`, `Divergence`, `Main` (each
  reported "Built"), plus the root module. "Build completed successfully (8662 jobs)."
  Toolchain `leanprover/lean4:v4.32.2`, Mathlib rev `v4.32.2`.
* `lake env lean AxiomCheck.lean`: each of the **nine theorems** depends only on `propext`,
  `Classical.choice`, `Quot.sound`: `flowDiv_eq_w`, `flowDiv_eq_w_all`, `flow_identity`,
  `flow_nonneg_combination`, `fEdge_div`, `conjecture_3_30_certificate`, `w_eq_U_mul_a`,
  `fEdge_nonneg`, `F_nonneg`.
* No `sorry`, `axiom`, `native_decide`, `skipKernelTC`, `implemented_by`, `@[extern]` or
  `unsafe` in `lean/ChowCone*`.
* **Seven linter warnings, no error:**
  1. `Abstract.lean:66:5` variable `hU` not explicitly referenced
  2. `Abstract.lean:77:5` variable `hU` not explicitly referenced
  3. `Ratios.lean:90:51` unused simp argument
  4. `Divergence.lean:284:17` unused simp argument
  5. `Divergence.lean:397:6` `push_neg` deprecated
  6. `Main.lean:72:25` variable `hp1` not explicitly referenced
  7. `Main.lean:136:6` variable `x` not explicitly referenced

  Warnings 1 and 2 mean that the hypothesis `hU : ∀ v, U v ≠ 0` of the final theorem is not
  needed by the proof (Lean's division by zero is zero, and the identity is algebraic). The
  hypothesis is true in the application and makes the stated theorem weaker, not unsound.

No Lean source has changed since that build. Old log for comparison: `lean/AxiomCheck.txt`
(2026-08-24) records the same nine lines.

## Python tests

* 2026-11-20, `manuscript-language-pass`: `python3 -m pytest tests/` gave 393 passed,
  1 failed in 197 s. The failure was `tests/test_weights.py::test_no_floating_point_in_sources`.
* 2026-11-21, `functional-scan`: **509 passed, 0 failed.**

How the one failure was resolved. The test banned every `/` token in `src/`, and
`src/k4_weights.py` line 63 divides a sum of `Fraction` objects by an integer. That is exact
arithmetic, and the `K4_*.md` notes record it as a known, deliberately untouched failure. The
obvious repair, rewriting that line, was not made: the SHA-256 of `src/k4_weights.py` is
recorded in the `source_provenance` of two frozen manifests
(`results/k4_degree4_decision/manifest.json`, `results/k4_width3_discovery/manifest.json`),
and all 14 pinned source hashes in those manifests match the current files. Instead:

* the ban on `/` stays for every other file and line; the single exception is tied to the
  exact text of that line and the test fails if the exception is not used;
* `test_the_allowed_division_is_exact_rational_arithmetic` recomputes the quantity with
  integers only for `1 <= d <= 30` and requires an identical `int`;
* `tests/test_source_provenance.py` requires every source pinned by a frozen manifest to be
  unchanged.

No check was disabled. The alternative, replacing `/ tot` by multiplication with
`Fraction(1, tot)`, would also make the old test pass but would invalidate the pinned hash.

## Functional scan (2026-11-21)

    python3 src/run_functional_scan.py 20 16 10 --witnesses results/functional_scan/witnesses.jsonl.gz
    python3 src/verify_functional_scan.py 8 --witnesses results/functional_scan/witnesses.jsonl.gz

Verifier output: 100 tail flows, 3 absolute-deviation flows, 17 absolute-deviation cuts;
153 stored flows, 22 stored cuts, 120 brute-force verdicts; 0 problems; exit status 0. With one
stored cut deliberately corrupted the verifier exits with status 1.

A second run reproduced every output byte for byte.

| file | SHA-256 |
|---|---|
| `results/functional_scan/summary.json` | `f79df8770b8bfdafde79241c7c9ce4dd20a384c89a9c283bf6019e3eaaa2c621` |
| `results/functional_scan/cuts.json` | `5a97fc9f4332dafa60191738d477041a49f859a49490b021494bf293a7afc65c` |
| `results/functional_scan/flows.json` | `0c761455f9e8dbd855b3f041053433b56625df5e8abeafd46231cf618faf94d7` |
| witness archive, uncompressed (9851019 bytes, 120 lines) | `0d94b04493c1d24e765929354d9ee1191ccba0d1a9896c159af6517ead910e1b` |
| witness archive as written here (zlib 1.2.12) | `329ff1a5b2db16444c5cb9327c799cd6e4636d9875b069cb3bba84feb1ef28a3` |

The digest of the compressed archive can differ between zlib versions; the uncompressed
digest cannot, and it is the one quoted in the manuscript.

Cross-check with an independently written implementation (review pack of 2026-11-21, not
part of this repository; archive SHA-256
`0eca8becaedda56473dd664bc829362255c496124b376746929e6fb89b349931`, its witness file
`1eac5a63e5ae745ad48bcfd6b1b75af9c011e180d77bf5f9765738187b35a583`):

* its verifier, run on the witness archive written here: PASS, all 120 cases;
* `verify_functional_scan.py --witnesses`, run on its witness file: 0 problems, all 120 cases;
* the two witness sets agree on every verdict and differ as flows in 76 of the 120 cases.

## `k = 4`

The finite checks in the test suite do not replace the two reviews below, and neither review
replaces a human referee or a formal proof.

* 2026-11-20, audit by the assistant in a fresh session (note `K4-AUDIT-2026-11-20.md`,
  delivered outside this repository): every identity, consumption and margin of
  `PROOF_K4_FOURTH_MOMENT.md` rederived; the step from the certificate to matroids compared
  with seven statements of Cheng–Lin's paper; no substantive gap found. A separate program
  written from the proof text, keeping every primitive label apart, passes for
  `3 <= d <= 20`: largest cascade totals `74.804` (bound 75) and `58.312` (bound 60).
* 2026-11-21, independent review pack: recommends keeping the `k = 4` theorem and proposes
  five edits to the manuscript, all applied. Its own cascade check covers 6,755 tagged debits
  on 4,180 targets for `3 <= d <= 20` and finds the same maxima,
  `143289723347/1915538625` and `4688570972/80405325`.

Both reviews are by AI systems. The first used the same model family that helped draft the
proof.

## Manuscript (2026-11-21)

`latexmk -pdf CHOW_CONE_FLOWS_MANUSCRIPT.tex` builds with no undefined reference and no
overfull box; 15 pages. Changes since `manuscript-language-pass`:

* new §11 (finite verification for all even moments) and a reproducibility subsection in §12;
* Conjecture 3.30 stated "for every `d >= 1`" in the abstract and introduction; the rank-one
  sentence of Corollary 11.4 corrected (both sides equal `φ(0)`; they do not both vanish);
* the flag variable `F_J` is used only on the support, with coefficients extended by zero;
* the support reduction is argued in both directions after Proposition 11.3;
* Table 1 in §8 lists the six types of charge, and the cases `M = 4` and `M = 5` are separated;
* the Lean paragraph states what was compiled and the number of warnings.

Author and date lines were not touched.

## Reading of the notes (2026-11-21)

Read in full: `STATUS.md`, `REPORT.md`, `RESEARCH_NOTES.md`, `PROOF_CONJECTURE_3_30.md`,
`PROOF_K4_FOURTH_MOMENT.md`, `K4_MATROID_BRIDGE.md`, `K4_NOTES.md`, `K2_K4_PAPER_OUTLINE.md`,
`PROOF_DEPENDENCY_MAP.md`, `LEAN_CORRESPONDENCE.md` and the nine `K4_*.md` gate reports.
`ARXIV_PROOF_DRAFT.md`: statement, structure, final sections and every status sentence; its
proof body repeats `PROOF_CONJECTURE_3_30.md` and was not re-read line by line. Source and
test files were swept by pattern, not read.

* No credentials, personal data, absolute paths or non-English text in tracked files. AI
  tools are named only in `README.md`, `PROVENANCE.md` and this file.
* Dated status sentences, references to the removed PDF and private commit hashes are
  explained in `README.md` ("How to read the dated notes") and `COMMIT_MAP.md`. The notes
  themselves were left as written.
* `LEAN_CORRESPONDENCE.md` names six declarations that do not exist under those names:
  `G_split_nonfinal`, `G_split_final_left`, `G_split_final_right`, `div`, `div_eq_w`,
  `div_eq_w_all`. The Lean sources have `G_splitAt_nonfinal`, `G_splitAt_final_left`,
  `G_splitAt_final_right`, `flowDiv`, `flowDiv_eq_w`, `flowDiv_eq_w_all`. The section
  "Verification requirements" of the same file uses the correct names. A patch was proposed
  to the author; it is **not applied** here.
* Informal wording such as "kill test", "by mandate" and "FULL MATROID THEOREM" was left
  unchanged.

## Content scan (2026-11-19; new and changed files re-scanned 2026-11-21)

* No credentials, tokens or keys in tracked text.
* No `.log`, `.env` or PDF file is tracked. `build-pdf/` and the witness archive are ignored.
* Third-party material: the Cheng–Lin PDF was removed from history. The repository quotes
  Cheng–Lin's definitions and statements, nothing else.
* Commit metadata, which becomes public with the history: author names, machine-local
  addresses that include host names, and one placeholder in place of an e-mail address. See
  `RELEASE_TODO.md`, item 5.

## Not checked

* Priority, beyond an arXiv keyword search and one web search on 2026-11-19.
* A clean download of Mathlib on a second machine (about 7 GB; deliberately not done).
* The `k = 4` proof by a human or a proof assistant.
