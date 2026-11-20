# Provenance of the k=2 certificate

This file describes the traceable discovery process inside this project. It makes no claim
about priority in the literature.

Each statement is labelled by its source:

* **[repo]** — verifiable from this repository's files and commit history.
* **[author]** — stated by the author (Xichen Tang) from the ChatGPT conversation of
  2026-08-18, which is not part of this repository. The author re-read that conversation and
  confirmed these statements on 2026-11-20.

## Who contributed what

1. **Problem and coefficients: Cheng and Lin.** Conjecture 3.30, the coefficients $U_J$,
   $a_J$, the inequality of Corollary 3.28 and the monotonicity inequalities of Lemma 3.29 are
   from R. Cheng and W. Lin, arXiv:2603.21680v3. They report computer verification for
   $d\le 19$ (Remark 3.31). **[repo: `README.md`, pinned source]**

2. **Experimental pattern: this repository's exact computations.** Exact big-integer
   max-flow showed feasibility for every $d\le 25$, and the edge-restriction experiments
   showed that certificates supported only on peel-2 splits $n_i\to(2,n_i-2)$ or
   $(n_i-2,2)$ exist for every $d\le 25$, while `peel2_left` alone fails at $d=3$. The
   decision-gate report stated the "peel2 conjecture" and had no uniform formula.
   **[repo: commits `ac60a2e` (2026-08-18 12:32:32 UTC) and `2a9cb9f` (12:33:41 UTC),
   `REPORT.md` items 6 and "peel2 conjecture", `results/stage3_restrictions.json`,
   `results/stage3_peel2_d21-25.json`]**
   These commits carry `Co-Authored-By: Claude` trailers: the computations were written and
   run with Claude Code as coding assistant.

3. **Uniform candidate: ChatGPT, in conversation with the author.** The author took the
   experiment report to a ChatGPT conversation at 12:35 UTC on 2026-08-18. At 12:40:59 UTC
   ChatGPT, combining the peel-2 pattern with Cheng–Lin's coefficients, proposed the
   explicit candidate: on the designated peel-2 moves take flow $G(\mathrm{child})$, with
   $G(\mathbf n)=U_J\prod_i(n_i-1)$. The original candidate already stated the final-block
   multiplicity: when the final block $4$ splits as $4\to(2,2)$, the left and right moves
   land on the same Boolean cover edge, each contributes $G(\mathrm{child})$, and the edge
   carries $2\,G(\mathrm{child})$. **[author]**
   The repository records the candidate as "proposed externally" (`RESEARCH_NOTES.md` §9,
   `PROOF_CONJECTURE_3_30.md`, commit `d3fb1f6`). The timing is consistent with the commit
   history: the report was committed at 12:33:41 UTC and the audit of the candidate at
   12:54:49 UTC. **[repo]**

4. **Audit and proof: this repository.** Commit `d3fb1f6` (2026-08-18 12:54:49 UTC)
   re-derived $w(c)=G(c)\sum_i\rho(n_i)$, the three ratio identities, and the in-edge
   bijection (Lemma 2), added an independent generator `src/explicit_certificate.py` that
   assigns flows by the closed formula, and checked divergence $=w_J$ at every support node
   for $d\le 25$. Commit `e0e64a3` (22:10:36 UTC) hardened Lemma 2 after an adversarial
   re-audit. Both carry `Co-Authored-By: Claude` trailers. **[repo]**

5. **Blind informal check: Rethlas.** After the audit, a Rethlas verification run on the
   finished proof text returned verdict "correct" with no gaps, and a second run examined
   Lemma 2. The files are `blind_request.json`, `blind_verdict.json` and
   `rethlas-chenglin-lemma2/lemma2_verdict.json` in a separate local directory, with local
   modification times 17:21–17:48 on 2026-08-18, after `d3fb1f6` and before `e0e64a3`. This
   is an LLM review, not a proof assistant. Rethlas did not produce the peel-2 experiments
   and did not perform the audit of step 4. **[author; local files outside this repository]**

6. **Formal certification: Lean 4.** Commit `131daca` (2026-08-21) machine-checks the
   combinatorial core; see `LEAN_CORRESPONDENCE.md` and `RELEASE_CHECKS.md`. **[repo]**

## Candidate versus the proved certificate

Compared: the candidate as confirmed by the author and as recorded in `RESEARCH_NOTES.md`
§9; the certificate of `PROOF_CONJECTURE_3_30.md` §3 at `d3fb1f6`; the generator
`src/explicit_certificate.py` at `d3fb1f6`; the Lean definitions `indN`, `indFL`, `indFR`,
`F` in `lean/ChowCone/Flow.lean`.

| aspect | candidate | proved certificate (`d3fb1f6`) | Lean |
|---|---|---|---|
| potential | $G(\mathbf n)=U_J\prod_i(n_i-1)$ | same | `G`, with `w_eq_U_mul_a` |
| nonfinal block $n_i\ge4$ | left peel $n_i\to(2,n_i-2)$, flow $G(\text{child})$ | move (N), same | `indN`: `i+1 < length`, `p = 2`, `4 ≤ c_i` |
| final block $n_r\ge4$ | both peels, flow $G(\text{child})$ each | moves (FL) $n_r\to(2,n_r-2)$ and (FR) $n_r\to(n_r-2,2)$ | `indFL` (`p = 2`), `indFR` (`p = c_i − 2`) |
| final block $n_r=4$ | the two moves are the same cover edge $4\to(2,2)$; edge weight $2\,G(\text{child})$ | same: (FL) and (FR) coincide and the flow is $2\,G(\text{child})$ | `F = (indN + indFL + indFR) · G(child)`: both indicators fire, giving `2·G` |
| blocks of size 2 or 3 | no outgoing flow | no selected move | all indicators require `4 ≤ c_i` |

Findings:

* **The proved certificate is the candidate, unchanged.** The audit of 2026-08-18 made no
  correction to the formula. The final-block multiplicity was part of the original
  candidate; the audit recorded it explicitly (commit `d3fb1f6`, items D and H) and proved
  that it is forced: with $G$ instead of $2G$ on the edge $4\to(2,2)$ the divergence
  identity fails at the child, which has two $2$-blocks at positions $r-1,r$.
* **No change between `d3fb1f6` and the final proof.** `e0e64a3` adds two paragraphs to the
  proof of Lemma 2 (distinct children, no edge aliasing) and a test file; the certificate
  definition is untouched. The Lean definitions agree with it clause by clause.
* The asymmetry between nonfinal blocks (left peel only) and the final block (both peels) is
  consistent with the experiments: `peel2_left` alone is infeasible from $d=3$.

## What this attribution does not claim

It describes how the result was found within this project. It does not assert that the
certificate is absent from the literature, and it does not replace a priority check.
