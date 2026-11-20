# Release checks (Xichen Tang's Mac; run by the assistant)

Checks are dated. "Old log" marks anything not run on the stated date. Original worktrees
were not modified.

## Branch head mapping (private repo -> this clone, after removing `paper/cheng-lin-v3.pdf`)

| branch | private head | this clone |
|---|---|---|
| `main` (frozen k=2 proof + Lean + hygiene commit) | `65e1056` | `38e2817` |
| `k4-fourth-moment` | `6360104` | `f92b24a` |
| `manuscript-language-pass` | `34317b9` | `f27e70d` |
| `external-referee-dc87a7b` (referee snapshot, no `lean/`) | `dc87a7b` | `21c7bbe` |
| `functional-scan` (new, 2026-11-20; exists only in this clone) | — | based on `f27e70d` |

`git rev-list --objects --all | grep cheng-lin-v3.pdf` returns nothing in this clone.

## Lean, k=2 (2026-11-19, from-scratch compile of the project modules)

Correction to the first version of this file: the first `lake build` of 2026-11-19, run in
the private worktree, reported the project modules as "Replayed". That is a cache hit: Lake
confirmed that the stored build products match the current sources, and `#print axioms` was
evaluated against those stored products. Nothing was recompiled in that run.

The check that counts is the second one, run the same day in this clone:

* `lean/` here is byte-identical to the private worktree's `lean/` (`diff -rq`), and is
  identical on `main`, `manuscript-language-pass` and `functional-scan`.
* The Mathlib package directory was cloned copy-on-write from the private worktree
  (`cp -cRp`, APFS). `lake build --no-build Mathlib` reported "All targets up-to-date
  (8654 jobs)", so Mathlib itself was **reused from cache, not recompiled**.
* `lake build` then compiled the **six project modules** from source, with no prior build
  directory: `ChowCone.Abstract`, `Basic`, `Flow`, `Ratios`, `Divergence`, `Main` (each
  reported "Built"), plus the root module. "Build completed successfully (8662 jobs)."
  Toolchain `leanprover/lean4:v4.32.2`, Mathlib rev `v4.32.2`.
* `lake env lean AxiomCheck.lean`: each of the **nine theorems** depends only on
  `propext`, `Classical.choice`, `Quot.sound`:
  `flowDiv_eq_w`, `flowDiv_eq_w_all`, `flow_identity`, `flow_nonneg_combination`,
  `fEdge_div`, `conjecture_3_30_certificate`, `w_eq_U_mul_a`, `fEdge_nonneg`, `F_nonneg`.
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

  Warnings 1 and 2 mean the hypothesis `hU : ∀ v, U v ≠ 0` of the final theorem is not
  needed by the proof (Lean's division by zero is zero, and the identity is algebraic). The
  hypothesis is true in the application and makes the stated theorem weaker, not unsound.

Old log for comparison: `lean/AxiomCheck.txt` on `main` (2026-08-24) records the same nine
lines.

## Python tests (2026-11-20, branch `manuscript-language-pass`, head `f27e70d`)

Full suite, including every k=4 test: `python3 -m pytest tests/` gave
**393 passed, 1 failed in 197 s**.

The one failure is `tests/test_weights.py::test_no_floating_point_in_sources`, unchanged
from 2026-11-19: the test rejects any `/` token in `src/`, and `src/k4_weights.py:63`
divides `Fraction` objects (exact arithmetic, not floating point). It reproduces in the
private worktree. It is a defect of the hygiene test's scope, not of a computation, but the
README sentence "a test statically rejects any floating point in `src/`" is not true of this
branch until the test or that line is changed. On `main` (`38e2817`) the suite has no k=4
sources and gives 172 passed.

Branch `functional-scan` (2026-11-20): `tests/test_functional_scan.py` adds 100 tests, all
passing; the three new source files contain no `/`, no float literal and no `float`.
`python3 src/verify_functional_scan.py`: 153 flows, 22 cuts and 120 brute-force verdicts
checked, 0 problems, exit status 0; with one cut deliberately corrupted it exits with
status 1.

## k=4

See the separate audit note `K4-AUDIT-2026-11-20.md` (delivered outside the repository).
The finite checks above do not replace the two audits recorded there.

## Manuscript

`latexmk -pdf CHOW_CONE_FLOWS_MANUSCRIPT.tex` builds without undefined references or
overfull boxes on `functional-scan` (2026-11-20). `build-pdf/` is untracked.

## Content scan of this clone (2026-11-19; new files re-scanned 2026-11-20)

* No credentials, tokens or keys in tracked text.
* No absolute private paths (`/Users/...`, `/home/...`) in tracked files, including the new
  scan sources and JSON results.
* No `.log`, `.env` or PDF files tracked.
* Third-party material: the Cheng–Lin PDF was removed from history. The repository quotes
  Cheng–Lin's definitions and statements, nothing else.
* Commit e-mails: machine-local addresses on the historical commits (not linkable to
  GitHub) and one literal placeholder in place of an address on `f27e70d`. Commits on
  `functional-scan` use the name `Xichen Tang` and an address set in this clone's
  local git config only.
* AI assistance: historical commits carry `Co-Authored-By: Claude` trailers; see
  `PROVENANCE.md`.

## Not checked

* Priority beyond an arXiv keyword search and one web search on 2026-11-19 (no follow-up to
  Cheng–Lin found; arXiv still serves v3).
* A clean download of Mathlib on a second machine (deliberately not done: about 7 GB).
