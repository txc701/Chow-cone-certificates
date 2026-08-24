# STATUS

**Current stage: PROOF.** An externally proposed explicit uniform peel2
certificate passed the full audit protocol (RESEARCH_NOTES.md §9) and is
written up as a self-contained proof: **PROOF_CONJECTURE_3_30.md** —
Conjecture 3.30 holds for every $d\ge1$, with explicit coefficients
$\lambda_{(J,J\cup\{j\})}=G(c(J\cup\{j\}))$. Machine-corroborated at every
node for $d\le25$; the staircase identities and shell decomposition are now
corollaries for all $d$. **Pending: external human review.**

**Lean certification (2026-08-21, commit `131daca`):** the combinatorial
core is machine-checked in Lean 4 (`lean/`, mathlib v4.32.2): divergence
identity `div f = w` for every `d ≥ 1` (support and full lattice), flow
nonnegativity, the three ratio lemmas, the in-edge classification, the
abstract nonnegative-combination lemma, and the assembled
`conjecture_3_30_certificate` on the Fintype of compositions with
Lemma 3.29 as external hypothesis. No sorry/admit/custom axioms;
`#print axioms` = standard trio for all nine load-bearing theorems
(`LEAN_CORRESPONDENCE.md`). Formalization stopped at the mandated point.

**Branch `k4-fourth-moment` (separate discovery work):** the k=4 analogue
is feasible for all d ≤ 20 (new conjecture), but the k=2 structure
deforms — staircases slack, shells crossed, peel2 dead, peel-width ≤ 3
suffices (see `K4_NOTES.md` on that branch). Does not bear on the frozen
k=2 proof.

Earlier gate summary (still accurate as history): feasibility for every
$d\le25$ reproduced the authors' $d\le19$ and extended it; Stage 3 found the
staircase/shell structure and the peel2 conjecture that the explicit
certificate now explains.

## Completed and mechanically verified

- [x] Two genuinely independent weight implementations
      (`src/weights_bitmask.py`, `src/weights_recursive.py`) agree exactly for
      $d\le5$; all $U_J,a_J,w_J$ integral (exact divisibility asserted);
      $\sum_J w_J=0$ for $d\le5$; hand calculations for $d=1,2,3$ pinned in
      tests; no floating point anywhere in `src/` (statically enforced by a
      tokenizer test).
- [x] All order ideals enumerated for $d\le5$ (counts = Dedekind numbers
      3, 6, 20, 168, 7581); $\min_{\mathcal D}\sum_{\mathcal D}w_J=0$ in every
      case ⇒ ideal condition holds for $d\le5$.
- [x] Exact big-integer Dinic max-flow; full-lattice network and reduced
      support-DAG network agree with each other and with the ideal oracle for
      $d\le5$ (value, feasibility, deficit): all feasible, supplies
      $S=0,6,20,90,840$ for $d=1..5$.
- [x] Extracted flows satisfy the divergence identity
      $\operatorname{div}f=w_J$ at every node (certificate property).
- [x] Results artifact: `results/stage1_oracle_d1-5.json`.

## Mathematical proofs (prose, RESEARCH_NOTES.md)

- [x] Prop. 1: Conjecture 3.30 ⟺ nonnegative flow on upward cover edges with
      divergence $w$ (§2; includes reduction from arbitrary nested pairs to
      covers and the sign/orientation audit).
- [x] Prop. 2: flow ⟺ every downward-closed ideal has $\sum w\ge0$, via
      max-flow/min-cut; finite INF $=S+1$ proven safe; min-cut ↔ ideal
      dictionary cap $=S+\sum_{\mathcal D}w$; failed min-cut ⇒ explicit
      negative ideal (§3).
- [x] Prop. 3: support reduction to all-parts-$\ge2$ compositions preserves
      the max-flow value (§4) — this is what makes $d\approx20$ tractable
      (Fibonacci-many nodes instead of $2^d$).

## Stage 2 (complete)

- [x] Implementation-agreement tests re-widened before the run: dual weight
      maps agree for $d\le11$; support map matches the full map for $d\le11$;
      full-lattice and support-DAG max-flows agree for $d\le11$
      (81 tests pass).
- [x] Progressive per-$d$ exact max-flow on the support DAG, one process per
      $d$ (`src/run_flow.py`), machine-readable `results/flow_dXX.json` with
      wall time and peak RSS for every $d=1..25$. **All FEASIBLE.**
- [x] Resource profile (~×2.2 time, ~×1.62 RSS per dimension; Fibonacci node
      growth): d=19: 0.66 s / 30 MiB; d=22: 7.0 s / 80 MiB;
      d=25: 63 s / 333 MiB. Capacities up to 90 bits ⇒ exact big-int
      arithmetic was genuinely required (int64 would have overflowed at
      $d\ge18$, where $S$ exceeds 63 bits).
- [x] $\sum_J w_J=0$ verified exactly for every $d\le25$ (support sum).

## Stage 3 (complete)

- [x] 4 deterministic edge-order heuristics ⇒ genuinely distinct integral
      certificates for $d=4..12$ (`results/certificates/`, 36 files); rigid
      skeleton is tiny (5–8 edges) ⇒ certificates are far from unique.
- [x] Edge-restricted families: `peel2` feasible for **all $d\le25$**
      (structural conjecture); `peel23` for all $d\le20$; `largest_block`
      dies at $d=15$; first/last/balanced die at $d=4$
      (`results/stage3_restrictions.json`, `stage3_peel2_d21-25.json`).
- [x] Staircase tight principal ideals characterized exactly ($d\le14$,
      regression-tested $d\le10$); shell identities verified $d\le25$;
      forced shell decomposition of every certificate confirmed on all 2313
      saved flow edges (`results/stage3_analysis.json`,
      `tests/test_structure.py` — 28 new tests, 109 total, all pass).
- [x] Tight-cut lattice via Picard–Queyranne for $d\le16$
      (`results/stage3_tightcuts.json`): SCC counts 4→51; non-principal
      tight ideals exist.
- [x] Failed ideas logged (RESEARCH_NOTES.md §9): U-proportional cascades
      (plain + pruned), largest-block, first/last/balanced-only.

## Blockers

None.

## Branch disposition

Conjecture 3.30 and its Lean certification stop at the completed combinatorial
core, pending external human review. Fourth-moment discovery is isolated on
the existing `k4-fourth-moment` branch; its future questions are recorded in
`K4_NOTES.md` there.
