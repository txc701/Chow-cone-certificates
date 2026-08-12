# STATUS

**Current stage:** Stage 1 complete; flow/ideal equivalence proofs written and
reviewed. Next: Stage 2 (progressive exact max-flow reproduction toward
$d\le19$) — **not started**, awaiting go-ahead.

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

## Blockers

None.

## Next decision

Start Stage 2: progressive per-$d$ support-DAG max-flow with wall-time and
peak-RSS recording, $d=1,\dots,19$; then decide about $d=20$ (and only then
$21/22$) from the recorded resource profile. Before the large run, re-widen
the implementation-agreement tests beyond $d\le5$ (they were deliberately
capped to match the Stage-1 scope).
