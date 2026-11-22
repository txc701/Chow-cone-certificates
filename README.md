# Nonnegative flows for Chow-polynomial moments of matroids

> **Release `v1.1`, 22 November 2026.** The paper is `CHOW_CONE_FLOWS_MANUSCRIPT.tex`
> (Xichen Tang, *Nonnegative flows for Chow-polynomial moments of matroids*). It refers to
> this repository at the tag `v1.1`. Its arXiv identifier will be added here once it exists.
> Release `v1.1` adds to `v1.0` the Lean formalization of the combinatorial core of the
> `k = 4` proof, and the passages of the manuscript and of the documents here that describe
> it. Nothing under `src/`, `tests/` and `results/` and no `k = 2` Lean source changed.

This repository studies the probability distribution defined by the Chow polynomial of a
loopless matroid, following R. Cheng and W. Lin, *Inequalities for Chow polynomials and Chern
numbers of matroids*, arXiv:2603.21680v3. Cheng and Lin conjecture that every central moment
of that distribution is at most the corresponding moment for the Boolean matroid of the same
rank (their Conjecture 3.14), and that the variance case has a specific kind of certificate:
the flag inequality is a nonnegative linear combination of their monotonicity inequalities
`N_J/U_J <= N_J'/U_J'` (their Conjecture 3.30, which they checked by computer for `d <= 19`).

## What is here, and how far each part is verified

| | Statement | Where | Verification |
|---|---|---|---|
| 1 | **Conjecture 3.30 for every `d >= 1`**, by an explicit flow `f = G(child)` on "peel-2" cover edges | `PROOF_CONJECTURE_3_30.md`, manuscript §4 | Symbolic proof. Its combinatorial core is machine-checked in Lean 4 (`lean/`), with Cheng–Lin Lemma 3.29 as an explicit hypothesis. |
| 2 | **The case `k = 4` of Conjecture 3.14**: the fourth central moment is at most the Boolean one, with a flag-level certificate of peel width at most 3 | `PROOF_K4_FOURTH_MOMENT.md`, `K4_MATROID_BRIDGE.md`, manuscript §§5–9 | Symbolic proof. Its combinatorial core (manuscript §§6–9: the flow, its divergence, its nonnegativity, the cases `d = 1, 2` and the final identity) is machine-checked in Lean 4 (`lean/ChowCone/K4/`), with Cheng–Lin Lemma 3.29 as an explicit hypothesis; the agreement of the Lean definitions with the manuscript has not been reviewed independently (`K4_LEAN_CORRESPONDENCE.md`). The tests here check the construction exactly for small `d`. An AI audit in a fresh session and two separately written checking programs, none of them part of this repository, found no gap up to `d = 20` (`RELEASE_CHECKS.md`). **It has not been refereed by anyone other than the author.** |
| 3 | **Conjecture 3.14 for every `k`, for matroids of rank 2 to 21** | `FUNCTIONAL_SCAN.md`, manuscript §11 | Exact computation: 100 instances, each with an explicit witness that is checked without a solver, cross-checked against an independently written implementation. Finite; it proves nothing for larger rank. |
| 4 | The absolute deviation `E|X_M - d/2|` has **no** certificate of this kind for `4 <= d <= 20` | same | Exact computation with explicit witnesses. This is a limit of the method. It is **not** a matroid counterexample. |
| 5 | The exact computations and failed searches behind 1 and 2 | `src/`, `results/`, `tests/`, `RESEARCH_NOTES.md`, `K4_*.md` | Exact integer or rational arithmetic throughout. |

The manuscript `CHOW_CONE_FLOWS_MANUSCRIPT.tex` contains 1 to 4.

Every statement about matroids rests on two results of Cheng and Lin that are **not**
re-proved here: their flag expansion of the Chow polynomial (Proposition 3.26) and their
monotonicity lemma (Lemma 3.29).

## The Lean theorems

`lean/ChowCone/Main.lean` (Lean `v4.32.2`, Mathlib `v4.32.2`) ends with

```lean
theorem conjecture_3_30_certificate (hn : 3 ≤ n)
    (N U : Composition n → ℚ) (hU : ∀ v, U v ≠ 0)
    (hmono : ∀ q c : Composition n, fEdge q c ≠ 0 → N q / U q ≤ N c / U c) :
    (∑ v : Composition n, (w v.blocks / U v) * N v
      = ∑ v : Composition n, ∑ u : Composition n,
          fEdge v u * (N v / U v - N u / U u))
    ∧ ∑ v : Composition n, (w v.blocks / U v) * N v ≤ 0
```

Here `n = d + 2`, `w` is Cheng–Lin's `U_J a_J` (proved equal in `w_eq_U_mul_a`), and `hmono` is
Lemma 3.29 restricted to the edges that carry flow. The theorem does not prove Lemma 3.29 and
does not mention matroids. It and the eight other load-bearing declarations depend only on
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`. The correspondence with
the prose proof is in `LEAN_CORRESPONDENCE.md`.

For `k = 4`, `lean/ChowCone/K4/Certificate.lean` ends with

```lean
theorem fourth_moment_coefficient_sum_nonpos (d : ℕ) (hd : 1 ≤ d)
    (N : Composition (d + 2) → ℚ)
    (hmono : ∀ q c : Composition (d + 2), fEdge4 d q c ≠ 0 →
      N q / U q.blocks ≤ N c / U c.blocks) :
    ∑ v : Composition (d + 2), a4d d v.blocks * N v ≤ 0
```

Here `a4d` is the coefficient `a_J^(4)` of the manuscript (equation (20)), `U` is the Boolean
flag number, and `fEdge4` is the flow of Theorem 9.1 of the manuscript. That the flow is
nonnegative, has divergence `w^(4)` and uses only splits `n -> (p, n-p)` with
`min(p, n-p) <= 3` is the theorem `uniform_fourth_moment_flow` in
`lean/ChowCone/K4/UniformFlow.lean`. As for `k = 2`, Lemma 3.29 is the hypothesis `hmono` and
matroids are not mentioned. The polynomial `S_4`, the constants `B_d` and the coefficient
`a^(4)` are entered as definitions; their derivation in §5 of the manuscript, and the step
from this inequality to the inequality of fourth moments, are not formalized. The axiom
report `lean/K4AxiomCheck.txt` lists 155 declarations, all on `propext`, `Classical.choice`,
`Quot.sound` or a subset of these; there is no `sorry`. The correspondence with the
manuscript is in `K4_LEAN_CORRESPONDENCE.md`. It was written by the AI assistant that wrote
the Lean proofs and has not been reviewed independently.

## What is not established

* The `k = 4` theorem has not been refereed by anyone other than the author. Its Lean
  formalization covers the combinatorial core only, and the agreement of the Lean
  definitions with the manuscript has not been reviewed independently.
* Neither Lean development contains matroid or Chow-ring theory: Cheng and Lin's flag
  expansion and Lemma 3.29 are used, not formalized.
* Conjecture 3.14 for `k` other than 2 and 4 is open beyond rank 21.
* Whether `E|X_M - d/2| <= E|X_d - d/2|` holds for matroids is not addressed.
* The description of the tight principal ideals as staircases (`RESEARCH_NOTES.md` §8) is
  empirical for `d <= 14` and is used by no proof.

## Reproduce

Python 3.10 or later; only `pytest` beyond the standard library.

```sh
python3 -m pip install pytest
python3 -m pytest tests/                        # full suite, about 3.5 minutes

python3 src/run_stage1_oracle.py                # d <= 5 oracle
python3 src/run_audit_explicit.py               # explicit k=2 certificate at every node, d <= 25

# all even moments, 1 <= d <= 20: verdicts, then one witness per instance, then the check
python3 src/run_functional_scan.py 20 16 10 --witnesses results/functional_scan/witnesses.jsonl.gz
python3 src/verify_functional_scan.py 8 --witnesses results/functional_scan/witnesses.jsonl.gz
```

Lean (needs `elan`; the Mathlib cache is about 7 GB):

```sh
cd lean
lake exe cache get
lake build                                      # the k = 2 modules
lake env lean AxiomCheck.lean                   # expect only propext, Classical.choice, Quot.sound
lake build ChowCone.K4.Certificate              # the nine k = 4 modules
lake env lean K4AxiomCheck.lean                 # compare with K4AxiomCheck.txt
```

Manuscript: `latexmk -pdf CHOW_CONE_FLOWS_MANUSCRIPT.tex`.

What was run, when, and with which result is recorded in `RELEASE_CHECKS.md`.

## Layout

* `CHOW_CONE_FLOWS_MANUSCRIPT.tex` — the paper.
* `PROOF_CONJECTURE_3_30.md`, `ARXIV_PROOF_DRAFT.md`, `PROOF_DEPENDENCY_MAP.md` — the `k = 2`
  proof, a standalone referee version, and its dependency map.
* `PROOF_K4_FOURTH_MOMENT.md`, `K4_MATROID_BRIDGE.md` — the `k = 4` certificate and the step
  from the certificate to matroids.
* `FUNCTIONAL_SCAN.md` — the finite verification for all even moments.
* `lean/` — the Lean project. `LEAN_CORRESPONDENCE.md` maps the `k = 2` part to the prose;
  `K4_LEAN_CORRESPONDENCE.md` maps the `k = 4` part, `lean/ChowCone/K4/`, to the manuscript.
* `src/` — exact computations. Weights (`weights_bitmask.py`, `weights_recursive.py`,
  `k4_weights.py`), the support DAG (`support.py`), max-flow with arbitrary-precision integers
  (`dinic.py`, `flows.py`), the explicit certificates (`explicit_certificate.py`,
  `k4_uniform_certificate.py`), the functional scan (`functional_scan.py`,
  `run_functional_scan.py`, `verify_functional_scan.py`), and the `k = 4` discovery gates
  (`k4_*`, `run_k4*`, `verify_k4*`).
* `results/` — machine-readable outputs. The two `manifest.json` files under `results/k4_*`
  record the SHA-256 of the sources that produced them; `tests/test_source_provenance.py`
  checks that those sources are unchanged.
* `tests/` — the test suite.
* `PROVENANCE.md` — who or what proposed each certificate: the `k = 2` candidate and its
  audit, the two steps of the `k = 4` construction, and the Lean formalization of `k = 4`.
* `RELEASE_CHECKS.md`, `COMMIT_MAP.md` — release records.
* `LICENSE`, `LICENSE-CC-BY-4.0` — the two licences; see "Licences" below.

## How to read the dated notes

`STATUS.md`, `REPORT.md`, `RESEARCH_NOTES.md`, `K4_NOTES.md`, `K2_K4_PAPER_OUTLINE.md` and the
`K4_*.md` gate reports are the research log, kept as written between 9 August and 1 September
2026. They are not updated retroactively, so three things in them need translation:

* **Status sentences are dated.** For example "Conjecture 3.30 remains open" in `REPORT.md`
  describes 18 August before the proof, and "new conjecture" for `k = 4` in `K4_NOTES.md`
  describes 21 August. The current status is this README.
* **"External human review is warranted before public claims"** appears in
  `PROOF_CONJECTURE_3_30.md` and `RESEARCH_NOTES.md`. No external human review has taken
  place. Since those lines were written the combinatorial core of the `k = 2` proof and, in
  release `v1.1`, that of the `k = 4` proof have been checked in Lean; neither proof has been
  checked by a person other than the author, as stated above.
* **Commit hashes are those of the private repository.** `COMMIT_MAP.md` translates them.
  One test, `test_no_floating_point_in_sources`, is reported as failing in several `K4_*.md`
  notes; `RELEASE_CHECKS.md` explains how it was resolved without changing the pinned source.

The notes also record the searches that failed: edge-restricted certificate families that die
at a specific `d`, the degree-4 mirror-invariant ansatz and its `d = 4` obstruction, and the
degree-4 desymmetrized ansatz that becomes inconsistent at `d = 11`. Each is a precise negative
statement about a defined class, with a stored witness.

## Sources and third-party material

Cheng and Lin's paper is cited, not redistributed. The notes refer to a pinned copy as
`paper/cheng-lin-v3.pdf`; that file is not in this repository. It is arXiv:2603.21680v3
(last revised 29 April 2026), 779,626 bytes, SHA-256
`b257b767f20e3ad16deebf9623698df4d88bc1b4c99deb2d195f693bcc1969ae`.

The public history was made from the private one by removing that file from every commit.
The first commit of the project (9 August 2026) contained nothing else and is therefore an
empty commit here. Dates and messages are unchanged. In the commit fields
the author's name is written uniformly as Xichen Tang and the e-mail is the author's GitHub
`noreply` address; the original fields had the name in two forms and machine-local addresses
that contained host names. Hashes differ (`COMMIT_MAP.md`).

## Licences

Copyright 2026 Xichen Tang.

* **Code and data: Apache License 2.0** (`LICENSE`). This covers `src/`, `tests/`, `lean/` and
  the machine-readable outputs in `results/`.
* **Text: Creative Commons Attribution 4.0 International** (`LICENSE-CC-BY-4.0`). This covers
  the manuscript `CHOW_CONE_FLOWS_MANUSCRIPT.tex` and every Markdown file in the repository.

Statements and notation quoted from Cheng and Lin's paper remain theirs; their paper is not
redistributed here.

## Provenance and use of AI tools

This work was carried out by Xichen Tang with AI tools, and they contributed substantively.
`PROVENANCE.md` states which step came from where.

* For the `k = 2` certificate: the problem and coefficients from Cheng and Lin, the peel-2
  pattern from this repository's computations, the uniform candidate from a ChatGPT
  conversation, and the audit, proof and Lean development from this repository, written with
  Claude Code. Several commits carry `Co-Authored-By` lines for that reason. The author
  states that the author audited the proof. The finished proof was also checked, without
  access to this repository, by the verification agent of Rethlas.
* For the `k = 4` certificate: the author's prompt named the method families, in a passage
  drafted by ChatGPT, and contained no formula for a flow. The signed identity and the
  rerouting that removes its negative terms were both derived by agents of OpenAI's Codex
  command-line tool in one session on 28 August 2026, which also wrote the proof text. Which
  of the agents proposed the rerouting first cannot be read from the surviving logs.
* For the Lean formalization of the `k = 4` certificate: it was written with Claude Code on
  21 and 22 November 2026 (`PROVENANCE.md`, Part 4).

The checks performed on the `k = 4` proof are AI audits, exact computations and the Lean
formalization of its combinatorial core, described in `RELEASE_CHECKS.md` and
`K4_LEAN_CORRESPONDENCE.md`; they are not a substitute for a referee.
