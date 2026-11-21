# Nonnegative flows for Chow-polynomial moments of matroids

> **Pre-release state.** This README describes the intended first public release (`v1.0`).
> Nothing has been published or tagged yet. The open items are listed in `RELEASE_TODO.md`.

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
| 2 | **The case `k = 4` of Conjecture 3.14**: the fourth central moment is at most the Boolean one, with a flag-level certificate of peel width at most 3 | `PROOF_K4_FOURTH_MOMENT.md`, `K4_MATROID_BRIDGE.md`, manuscript §§5–9 | Symbolic proof. The tests here check the construction exactly for small `d`. An AI audit in a fresh session and two separately written checking programs, none of them part of this repository, found no gap up to `d = 20` (`RELEASE_CHECKS.md`). **Not formalized. No human referee has read it.** |
| 3 | **Conjecture 3.14 for every `k`, for matroids of rank 2 to 21** | `FUNCTIONAL_SCAN.md`, manuscript §11 | Exact computation: 100 instances, each with an explicit witness that is checked without a solver, cross-checked against an independently written implementation. Finite; it proves nothing for larger rank. |
| 4 | The absolute deviation `E|X_M - d/2|` has **no** certificate of this kind for `4 <= d <= 20` | same | Exact computation with explicit witnesses. This is a limit of the method. It is **not** a matroid counterexample. |
| 5 | The exact computations and failed searches behind 1 and 2 | `src/`, `results/`, `tests/`, `RESEARCH_NOTES.md`, `K4_*.md` | Exact integer or rational arithmetic throughout. |

The manuscript `CHOW_CONE_FLOWS_MANUSCRIPT.tex` contains 1 to 4.

Every statement about matroids rests on two results of Cheng and Lin that are **not**
re-proved here: their flag expansion of the Chow polynomial (Proposition 3.26) and their
monotonicity lemma (Lemma 3.29).

## The Lean theorem

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
the prose proof is in `LEAN_CORRESPONDENCE.md`. The `k = 4` proof is not formalized.

## What is not established

* The `k = 4` theorem has no formal proof and no human referee.
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
lake build
lake env lean AxiomCheck.lean                   # expect only propext, Classical.choice, Quot.sound
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
* `lean/` — the Lean project; `LEAN_CORRESPONDENCE.md` maps it to the prose.
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
* `PROVENANCE.md` — who or what proposed the `k = 2` certificate, and how it was audited.
* `RELEASE_CHECKS.md`, `COMMIT_MAP.md`, `RELEASE_TODO.md` — release records.

## How to read the dated notes

`STATUS.md`, `REPORT.md`, `RESEARCH_NOTES.md`, `K4_NOTES.md`, `K2_K4_PAPER_OUTLINE.md` and the
`K4_*.md` gate reports are the research log, kept as written between 9 August and 1 September
2026. They are not updated retroactively, so three things in them need translation:

* **Status sentences are dated.** For example "Conjecture 3.30 remains open" in `REPORT.md`
  describes 18 August before the proof, and "new conjecture" for `k = 4` in `K4_NOTES.md`
  describes 21 August. The current status is this README.
* **"External human review is warranted before public claims"** appears in
  `PROOF_CONJECTURE_3_30.md` and `RESEARCH_NOTES.md`. No external human review has taken
  place. Since those lines were written the `k = 2` core has been checked in Lean; the `k = 4`
  proof has not been checked by a human or a proof assistant, as stated above.
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
empty commit here. Authors, dates and messages are unchanged; hashes differ (`COMMIT_MAP.md`).

## Provenance and use of AI tools

This work was carried out by Xichen Tang with AI tools, and they contributed substantively.
`PROVENANCE.md` states, for the `k = 2` certificate, which step came from where: the problem
and coefficients from Cheng and Lin, the peel-2 pattern from this repository's computations,
the uniform candidate from a ChatGPT conversation, and the audit, proof and Lean development
from this repository, written with Claude Code. Several commits carry `Co-Authored-By` lines
for that reason. The checks performed on the `k = 4` proof are AI audits and exact
computations, described in `RELEASE_CHECKS.md`; they are not a substitute for a referee.
