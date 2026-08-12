# STATUS

**Current stage:** Stage 2 complete — Conjecture 3.30's flow certificate is
**feasible for every $d\le25$** (exact arithmetic). This reproduces the
authors' $d\le19$ verification (Remark 3.31) and extends it by six
dimensions; no counterexample exists in this range. Next: Stage 3
(structural certificate and tight-cut extraction).

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

## Blockers

None.

## Next decision

Stage 3: extract structurally distinct integral certificates (varying
edge-order heuristics: earliest/latest block split, balanced/unbalanced,
lexicographic), translate edges to block splits $n_i\to(p,n_i-p)$, search for
local-data formulas validated against all $d\le25$; extract min/max tight
cuts from the residual graph.
