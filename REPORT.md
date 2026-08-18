# First decision gate report — computational kill test of Cheng–Lin Conjecture 3.30

**Target:** Conjecture 3.30 of R. Cheng & W. Lin, arXiv:2603.21680**v3** (pinned:
`paper/cheng-lin-v3.pdf`): the inequality $\sum_{J\subseteq[d]}a_JN_J\le0$
(Corollary 3.28) is a nonnegative linear combination of the monotonicity
inequalities $N_J/U_J\le N_{J'}/U_{J'}$, $J\subseteq J'$ (Lemma 3.29), for
every $d\ge1$. The authors verified $d\le19$ by computer (Remark 3.31).

**Headline result: the kill test failed to kill.** The conjecture's
certificate exists for **every $d\le25$** in exact integer arithmetic —
reproducing the authors' full verified range and extending it by six
dimensions — and the search surfaced new exact structure (staircase
identities, a forced shell decomposition, and a surviving "peel-2"
restricted-certificate conjecture) that points at a possible uniform proof
route. **Conjecture 3.30 remains open**; nothing here is a proof for all $d$.

All gate criteria are met: (1) two independent weight implementations agree;
(2) the flow/ideal equivalence is proved in prose (RESEARCH_NOTES.md §§2–4);
(3) exhaustive ideal enumeration agrees with max-flow for $d\le5$;
(4) feasibility reproduced through $d=19$ and beyond to $d=25$ well within
resource limits; (5) extensive structural extraction was performed.

---

## 1. Mechanically verified facts

*Exact integer arithmetic throughout; no floating point exists in `src/`
(enforced by a tokenizer test). Every claim is reproducible from the repo;
per-$d$ artifacts in `results/`.*

1. **Weights.** Two genuinely independent implementations of
   $J\mapsto(U_J,a_J,w_J)$ (bitmask-based and recursive-composition-based
   with different formulas) produce identical maps for $d\le11$; all values
   integral; hand calculations for $d=1,2,3$ match; $\sum_Jw_J=0$ exactly for
   $d\le25$.
2. **Oracle agreement ($d\le5$).** All downward-closed ideals enumerated
   (counts = Dedekind numbers 3, 6, 20, 168, 7581);
   $\min_{\mathcal D}\sum_{J\in\mathcal D}w_J=0$ in every case, and the
   max-flow decision, deficit, and feasibility agree exactly with the ideal
   oracle on both network formulations.
3. **Feasibility for $d\le25$** (`results/flow_dXX.json`): support-DAG
   max-flow equals total supply $S$ for every $d=1..25$; extracted flows
   satisfy $\operatorname{div}f=w_J$ at every node. Resources: $d{=}19$:
   0.66 s / 30 MiB; $d{=}22$: 7 s / 80 MiB; $d{=}25$: 63 s / 333 MiB.
   $S$ exceeds 63 bits from $d=18$ (90 bits at $d=25$): int64 solvers would
   overflow silently; big-int arithmetic was mandatory.
4. **Staircase tight ideals.** With $\sigma(T)=\sum_{J\subseteq T}w_J$:
   for all $T$ ($d\le14$): $\sigma(T)\ge0$, and $\sigma(T)=0$ exactly for
   $T_k=\{2,4,\dots,2k\}\cup\{2k+1,\dots,d\}$, $0\le k\le\lfloor d/2\rfloor$
   (element 1 free). Equivalent shell form — grouping support compositions
   by smallest odd element (with a residual class) makes every group sum to
   exactly 0 — verified for $d\le25$.
5. **Shell decomposition.** All 2313 flow edges across 36 heuristic
   certificates ($d\le12$) have zero shell crossings, as forced by fact 4
   plus the ideal argument.
6. **Restricted families.** `peel2` certificates (only splits
   $n_i\to(2,n_i-2)$ or $(n_i-2,2)$) exist for **all $d\le25$**; `peel23`
   for all $d\le20$; `largest_block` fails first at $d=15$; `first_block`,
   `last_block`, `balanced_only` fail at $d=4$; `peel2_left` at $d=3$.
7. **Non-uniqueness.** Four deterministic heuristics give distinct
   certificates from $d=6$; the rigid skeleton (edges with identical flow in
   all four) is 5–8 edges against union supports up to 401.
8. **Tight-cut lattice.** Picard–Queyranne residual SCC counts grow
   4→51 for $d=4..16$; non-principal tight ideals exist (e.g. at $d=8$ the
   complement of the up-set of $(3,3,4)$).

## 2. Mathematical proofs (prose, RESEARCH_NOTES.md §§2–4)

* **Prop. 1.** Conjecture 3.30 (identity-of-linear-forms reading) ⟺
  existence of a nonnegative flow $f$ on upward Boolean cover edges with
  $\operatorname{div}f(J)=w_J$ for all $J$; arbitrary nested pairs reduce to
  covers by chain decomposition. Signs and orientation audited.
* **Prop. 2.** Such a flow exists ⟺ every downward-closed ideal has
  $\sum_{\mathcal D}w_J\ge0$; via max-flow/min-cut with the exact dictionary
  $\operatorname{cap}=S+\sum_{\mathcal D}w_J$, deficit
  $=-\min_{\mathcal D}\sum_{\mathcal D}w_J$; the finite capacity
  $\mathrm{INF}=S+1$ is proved safe on both flow and cut sides; a failing
  min-cut constructively yields a negative ideal (the counterexample object —
  never triggered).
* **Prop. 3.** The reduction to the all-parts-$\ge2$ support DAG (Fibonacci
  many nodes instead of $2^d$) preserves the max-flow value. This is what
  made $d\le25$ cheap.
* **Shell-decomposition mechanism.** *Given* the staircase identities at a
  fixed $d$, the zero-crossing property of every certificate at that $d$ is
  proved (ideal + tightness argument). The identities themselves are proved
  only in the verified range (empirical beyond a fixed $d$ — see §3).

## 3. Empirical patterns (verified in range, unproved in general)

* The staircase identities $\sigma(T_k)=0$ for all $d$ (verified $d\le25$).
  The $k=0$ case is the paper's Corollary 3.28 identity; a
  generating-function proof of the general case looks plausible and would
  make the shell decomposition a theorem for all $d$.
* The staircase family is *exactly* the set of tight principal ideals
  (verified $d\le14$).
* **peel2 conjecture**: certificates supported on peel-2 splits exist for
  all $d$ (verified $d\le25$). This is the strongest surviving structural
  hypothesis and the recommended proof target: the peel2 DAG is much sparser
  and has domino-peeling recursive structure.
* Within shells, observed flows have a self-similar structure: the prefix up
  to the first odd cut point stays frozen; the tail refines like a smaller
  instance.

## 4. Speculative conjectures

* A uniform proof might proceed shell-by-shell by induction on $d$, using a
  product/transfer structure of $w$ along the frozen prefix and a smaller
  instance on the tail. Not yet formalized; the required factorization of
  $w$ is nontrivial ($a_J$ mixes a product with an additive term).
* The tight-cut distributive lattice (growing SCC counts) may admit a clean
  combinatorial description whose extreme rays certify all ideal
  inequalities at once. Unexplored beyond sampling.

## 5. Failed approaches (details in RESEARCH_NOTES.md §9)

* U-proportional cascade and its alive-pruned variant (explicit local
  forwarding rules): fail at $d=4/5$ resp. $d=5/8$, both by over- and
  under-supplying shared sinks. Demand-blind local rules cannot work.
* largest-block-only certificates: survive through $d=14$, die at $d=15$ —
  a concrete warning that patterns holding for a long initial range can
  fail; nothing in this report rests on small-range extrapolation alone
  without being labeled as such.
* first-block / last-block / balanced-only / left-peel-only: die at $d\le4$.

## 6. Recommended next steps

1. Prove the staircase identities $\sigma(T_k)=0$ for all $d$ (generating
   functions, following the paper's own proof of the $k=0$ case). This
   upgrades the shell decomposition to a theorem and factors the conjecture
   into per-shell statements.
2. Attack the peel2 conjecture: extract peel2 certificates per shell, look
   for an inductive construction on the sparser DAG.
3. Only after the above: consider the fourth-moment ($k>2$) generalization
   (explicitly out of scope for this gate).

## Reproducibility

```sh
python3 -m pytest tests/ -q          # 109 tests
python3 src/run_stage1_oracle.py     # d<=5 oracle
python3 src/run_flow.py <d>          # per-d feasibility (d<=25 tested)
python3 src/run_stage3.py            # restrictions/certificates/tight cuts
python3 src/run_peel2_ext.py         # peel2 d=21..25
python3 src/run_stage3_analysis.py   # staircase/shells/cascades/skeleton
```

Repository state at this gate: commit history `d11b5c7 → 4f0b233 → 347d017 →
892007d → 88e5448 → ac60a2e` (+ this report).
