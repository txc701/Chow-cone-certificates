# Research notes — Cheng–Lin Conjecture 3.30 (arXiv:2603.21680v3)

All references are to the pinned version `paper/cheng-lin-v3.pdf` (v3).

## 1. Pinned setup and sign conventions

Fix an integer $d \ge 1$. For $J=\{j_1<\cdots<j_m\}\subseteq[d]$ put $j_0=0$ and
associate the composition of $d+2$

$$n_i = j_i - j_{i-1}\ (1\le i\le m),\qquad n_{m+1}=d+2-j_m .$$

Every part satisfies $n_i\ge 1$, and the **last part always satisfies
$n_{m+1}\ge 2$** because $j_m\le d$. The map $J\mapsto(n_1,\dots,n_{m+1})$ is a
bijection between subsets of $[d]$ and compositions of $d+2$ with last part
$\ge 2$ (inverse: $J$ = set of proper prefix sums). Define

$$U_J=\frac{n_{m+1}\,(d+1)!}{\prod_{i=1}^{m+1}n_i!}\ (>0),\qquad
a_J=\prod_{i=1}^{m+1}(n_i-1)\cdot\Big(\tfrac12\sum_{i=1}^{m+1}n_i(n_i-3)\Big),\qquad
w_J=U_J\,a_J .$$

Both are integers: $U_J = \binom{d+2}{n_1,\dots,n_{m+1}}\cdot n_{m+1}/(d+2)$ is
the number of flags counted in the paper (denoted $N_J(U_{d+1})$, a cardinality),
and $\sum_i n_i(n_i-3)$ is even because $n(n-3)$ is a product of two integers of
opposite parity. (Our test suite checks integrality by asserting exact
divisibility before every division; no floating point exists in `src/`.)

For a matroid $M$ of rank $d+1$, $N_J$ denotes its number of flags of flats of
type $J$, and $N_J>0$, $U_J>0$. Write

$$x_J := \frac{N_J}{U_J}.$$

* **Lemma 3.29 (monotonicity).** $J\subseteq J' \implies x_J \le x_{J'}$.
  So along the Boolean lattice order, $x$ is non-decreasing **upward**.
* **Target inequality (Corollary 3.28 form).**
  $\sum_{J\subseteq[d]} a_J N_J \le 0$, i.e. $\sum_J w_J\,x_J\le 0$.
* **Corollary 3.28 identity.** $\sum_{J\subseteq[d]} a_J U_J=\sum_J w_J=0$
  (machine-checked exactly for $d\le5$ so far; the paper proves it in general).

**Conjecture 3.30 (pinned reading).** There exist coefficients
$\lambda_{(J,J')}\ge 0$, indexed by nested pairs $J\subsetneq J'$, such that

$$\sum_J a_J N_J \;=\; \sum_{J\subsetneq J'} \lambda_{(J,J')}\,
\Big(\frac{N_J}{U_J}-\frac{N_{J'}}{U_{J'}}\Big)
\qquad\text{identically as linear forms in } (N_K)_{K\subseteq[d]}. \tag{3.30}$$

Each bracket is $\le 0$ by Lemma 3.29, so (3.30) exhibits the target inequality
as a nonnegative combination of the monotonicity inequalities. We pin the
*identity-of-linear-forms* reading: "inequality $A$ is a nonnegative linear
combination of inequalities $B_i$" means the linear form of $A$ equals a
nonnegative combination of the forms of $B_i$. (Any scaling of the individual
inequalities, e.g. clearing denominators to $U_{J'}N_J-U_JN_{J'}\le0$, is
absorbed into $\lambda$ because all $U$'s are positive; the choice of scaling
does not change the existence question.)

## 2. Proposition 1 — Conjecture 3.30 ⟺ nonnegative flow with divergence $w$

**Definitions.** The *cover edges* of the Boolean lattice are
$J\to J\cup\{j\}$, $j\in[d]\setminus J$, oriented **upward** (toward larger
sets). For $f:\{\text{cover edges}\}\to\mathbb{R}_{\ge0}$ define the divergence

$$\operatorname{div}f(J) := \operatorname{outflow}(J)-\operatorname{inflow}(J)
=\sum_{j\notin J} f(J\to J\cup\{j\})-\sum_{j\in J} f(J\setminus\{j\}\to J).$$

**Proposition 1.** (3.30) holds for a given $d$ **iff** there is
$f\ge0$ on the cover edges with $\operatorname{div}f(J)=w_J$ for all $J$.

*Proof.* Substitute $N_K=U_K x_K$ in (3.30). Since the $U_K>0$ are fixed
constants, (3.30) is an identity of linear forms in $(N_K)$ iff the same
identity holds in the coordinates $(x_K)$, where it reads

$$\sum_J w_J\,x_J=\sum_{J\subsetneq J'}\lambda_{(J,J')}\,(x_J-x_{J'}). \tag{$\ast$}$$

Comparing the coefficient of $x_K$ on both sides, $(\ast)$ holds iff

$$w_K=\sum_{J'\supsetneq K}\lambda_{(K,J')}-\sum_{J\subsetneq K}\lambda_{(J,K)}
\quad\text{for every }K, \tag{$\ast\ast$}$$

i.e. iff $\lambda$, viewed as a nonnegative flow on the DAG of **all** nested
pairs, has divergence $w$.

(⇐, covers suffice) A nonnegative $f$ on cover edges with
$\operatorname{div}f=w$ is a special case of $\lambda$ (covers are nested
pairs), so (3.30) holds.

(⇒, reduction to covers) Given $\lambda\ge0$ satisfying $(\ast\ast)$: for each
nested pair $J\subsetneq J'$ fix arbitrarily a saturated chain
$J=C_0\lessdot C_1\lessdot\cdots\lessdot C_r=J'$ in the Boolean lattice and
note $x_J-x_{J'}=\sum_{t=1}^r (x_{C_{t-1}}-x_{C_t})$. Replacing every term of
$(\ast)$ by this telescoping sum rewrites the right side as a nonnegative
combination of cover terms only; equivalently, define
$f(e):=\sum_{(J,J')}\lambda_{(J,J')}\cdot\#\{t: e=(C_{t-1}\to C_t)\text{ in the
chain chosen for }(J,J')\}\ge0$. Divergence is linear in the flow and each
rerouted chain has the same divergence ($+1$ at $J$, $-1$ at $J'$, $0$
between) as the pair edge it replaces, so $\operatorname{div}f=w$. $\qquad\blacksquare$

**Orientation check.** Positive-weight nodes are *sources* of $f$
(net outflow), negative-weight nodes are *sinks*. Since $x$ increases upward
and flow runs upward, $\sum_J w_Jx_J=\sum_e f(e)\,(x_{\mathrm{tail}(e)}-x_{\mathrm{head}(e)})\le0$:
mass moves from low $x$ (coarse $J$, big blocks, $w>0$) to high $x$
(fine $J$, small blocks, $w<0$). Sanity example $d=2$:
$w_\varnothing=6>0$, $w_{\{2\}}=-6<0$, and indeed
$\varnothing\subset\{2\}$, $f(\varnothing\to\{2\})=6$ works.

A necessary condition for any divergence-prescribed flow is
$\sum_J w_J=\sum_J\operatorname{div}f(J)=0$ (every edge contributes $+f(e)$ at
its tail and $-f(e)$ at its head). This is exactly the Corollary 3.28 identity.

## 3. Proposition 2 — flow ⟺ order ideals (max-flow/min-cut, explicit signs)

An **order ideal** (downward-closed set) is $\mathcal D\subseteq 2^{[d]}$ with:
$J\in\mathcal D$ and $J'\subseteq J$ imply $J'\in\mathcal D$. Its complement
$\mathcal U=2^{[d]}\setminus\mathcal D$ is upward-closed, and conversely.

**Proposition 2.** For a given $d$ the following are equivalent:

1. there exists $f\ge0$ on cover edges with $\operatorname{div}f=w$;
2. every order ideal $\mathcal D$ satisfies $\sum_{J\in\mathcal D}w_J\ge0$.

Moreover, with the network $G$ defined below,
$\max\text{flow}(G) = S + \min_{\mathcal D}\sum_{J\in\mathcal D}w_J$, where
$S:=\sum_{w_J>0}w_J$; so the *flow deficit* equals
$-\min_{\mathcal D}\sum_{J\in\mathcal D}w_J$, and a minimum cut of value
$<S$ hands us a negative-weight ideal (Section 3.4).

### 3.1 (1) ⇒ (2): why upward flow forces nonnegative ideal sums

Let $f\ge0$ with $\operatorname{div}f=w$ and let $\mathcal D$ be an ideal. Sum
the divergence over $\mathcal D$. Edges with both ends in $\mathcal D$ cancel
($+f$ at the tail, $-f$ at the head); edges with both ends outside contribute
nothing. Hence

$$\sum_{J\in\mathcal D}w_J
=\underbrace{\sum_{\substack{e=(A\to B)\\ A\in\mathcal D,\,B\notin\mathcal D}}f(e)}_{\text{leaving }\mathcal D}
-\underbrace{\sum_{\substack{e=(A\to B)\\ A\notin\mathcal D,\,B\in\mathcal D}}f(e)}_{\text{entering }\mathcal D}.$$

The second sum is **empty**: a cover edge $A\to B$ has $A\subsetneq B$, so
$B\in\mathcal D$ forces $A\in\mathcal D$ by downward-closedness — no edge can
enter an ideal from outside. (This is where the upward orientation is used;
with the opposite orientation the same argument would apply to up-sets.)
Therefore $\sum_{J\in\mathcal D}w_J=\sum_{e\text{ leaving}}f(e)\ge0$. ∎

### 3.2 The network and the safety of the finite "infinite" capacity

Let $P=\{J:w_J>0\}$, $N=\{J:w_J<0\}$, $S=\sum_{J\in P}w_J$
($=\sum_{K\in N}(-w_K)$ by $\sum w=0$). Define the network $G$
(implemented in `src/flows.py::full_lattice_flow`):

* nodes: all $J\subseteq[d]$, plus source $s$ and sink $t$;
* $s\to J$ with capacity $w_J$ for $J\in P$;
* $J\to t$ with capacity $-w_J$ for $J\in N$;
* every cover edge $J\to J\cup\{j\}$ with capacity $\mathrm{INF}:=S+1$.

**Claim A (flow with divergence $w$ ⟺ max-flow $=S$).**
Given $f\ge0$ with $\operatorname{div}f=w$, extend it by sending $w_J$ on each
$s\to J$ and $-w_K$ on each $K\to t$. Conservation at $J\in P$:
inflow $=w_J+\text{in}_f(J)$, outflow $=\text{out}_f(J)$, and these agree
because $\operatorname{div}f(J)=w_J$; similarly at $K\in N$ and (trivially,
$\operatorname{div}f=0$) at zero-weight nodes. All source edges are saturated,
so the value is $S$, the obvious upper bound. Conversely a flow of value $S$
saturates every $s\to J$ and every $K\to t$ edge (their total capacities are
both exactly $S$), and reading conservation at each lattice node backwards
shows its restriction $f$ to cover edges satisfies $\operatorname{div}f=w$.
**Also every edge of $G$ carries flow $\le S<\mathrm{INF}$** in any admissible
flow: the lattice part of $G$ is a DAG, so the flow decomposes into $s$–$t$
paths, and each edge's flow is the sum of the values of the paths through it,
which is at most the total value $\le S$. So the finite bound never truncates
a flow.

**Claim B (INF is safe on the cut side).** The cut
$(\{s\},\ \text{everything else})$ has capacity $S$. Hence the minimum cut has
capacity $\le S<\mathrm{INF}$, so **no minimum cut contains a cover edge**, and
making cover capacities $\mathrm{INF}=S+1$ instead of genuinely infinite
changes neither the max-flow value nor the set of minimum cuts. Together with
Claim A: choosing any integer $\ge S+1$ is rigorous; we use exactly $S+1$.

### 3.3 (2) ⇒ (1): ideal inequalities + $\sum w=0$ imply a flow exists

Assume every ideal has nonnegative weight sum. We show
$\max\text{flow}(G)=S$; Claim A then produces the required $f$. (Integrality
of $f$ is free: all capacities are integers, so Dinic — and max-flow/min-cut
generally — returns an integral optimal flow.)

By max-flow/min-cut it suffices to show every cut has capacity $\ge S$. Let
$(\mathcal C\cup\{s\},\ \overline{\mathcal C}\cup\{t\})$ be a cut with
$s$-side lattice part $\mathcal C\subseteq 2^{[d]}$, of capacity $<\mathrm{INF}$
(cuts of capacity $\ge\mathrm{INF}\ge S+1>S$ need no argument). Then no cover
edge crosses from $\mathcal C$ to $\overline{\mathcal C}$: such an edge would
contribute $\mathrm{INF}$ by itself. So for $J\in\mathcal C$, **every** cover
successor $J\cup\{j\}$ lies in $\mathcal C$; iterating, $\mathcal C$ is
**upward-closed**, and $\mathcal D:=\overline{\mathcal C}$ is an ideal. The
edges that do cross are: $s\to J$ for $J\in P\setminus\mathcal C
= P\cap\mathcal D$, and $K\to t$ for $K\in N\cap\mathcal C$. Hence

$$\operatorname{cap} = \sum_{J\in P\cap\mathcal D}w_J
+\sum_{K\in N\cap\mathcal C}(-w_K).$$

Since $\sum_{K\in N}(-w_K)=S$ and $N=(N\cap\mathcal C)\sqcup(N\cap\mathcal D)$,
the second sum equals $S+\sum_{K\in N\cap\mathcal D}w_K$, giving

$$\operatorname{cap}
= S+\sum_{J\in P\cap\mathcal D}w_J+\sum_{K\in N\cap\mathcal D}w_K
= S+\sum_{J\in\mathcal D}w_J \tag{cut=ideal}$$

(zero-weight nodes contribute nothing). By hypothesis
$\sum_{J\in\mathcal D}w_J\ge0$, so $\operatorname{cap}\ge S$. Conversely the
cut with $\mathcal C=2^{[d]}$, $\mathcal D=\varnothing$ cuts exactly the sink
edges, with capacity $\sum_{K\in N}(-w_K)=S$; so min cut $\le S$. Hence
min cut $=S=$ max flow. ∎

Note where each hypothesis enters: the ideal inequalities give
$\operatorname{cap}\ge S$; the identity $\sum_Jw_J=0$ was used to rewrite
$\sum_{K\in N\cap\mathcal C}(-w_K)$ and, more fundamentally, is necessary for
any divergence-$w$ flow to exist at all (Section 2).

### 3.4 Failure certificate: min-cut → negative ideal

Formula (cut=ideal) is an exact bijective bookkeeping between cuts of finite
capacity and order ideals: $\text{capacity}=S+\sum_{\mathcal D}w$. Minimising
both sides:

$$\max\text{flow}=\min\text{cut}=S+\min_{\mathcal D\text{ ideal}}\ \sum_{J\in\mathcal D}w_J,
\qquad\text{deficit}:=S-\max\text{flow}=-\min_{\mathcal D}\sum_{J\in\mathcal D}w_J\ \ge 0.$$

If the max flow is $<S$, take any minimum cut — e.g. the standard one where
$\mathcal C\cup\{s\}$ = nodes reachable from $s$ in the residual graph
(`Dinic.min_cut_source_side`). Its capacity is $<S\le\mathrm{INF}-1$, so by
Section 3.3 the lattice part $\overline{\mathcal C}$ is an order ideal
$\mathcal D$ with

$$\sum_{J\in\mathcal D}w_J=\operatorname{cap}-S=\max\text{flow}-S=-\text{deficit}<0,$$

an explicit violation of (2) — this is the counterexample object we would
report. Conversely a negative ideal yields a cut of capacity $<S$, so
infeasibility is always certified in both languages simultaneously.

## 4. Support reduction (why large $d$ is tractable) — proved, machine-checked

$w_J=0$ whenever some part $n_i=1$, because of the factor $\prod_i(n_i-1)$ in
$a_J$. Let $\Sigma_{\ge2}(d)$ = compositions of $d+2$ with **all parts
$\ge2$** (these are $F(d+1)$-many, Fibonacci with $F(1)=F(2)=1$; e.g. 6765 for
$d=19$, 28657 for $d=22$); the support of $w$ is contained in the
corresponding set of subsets. The reduced DAG $H$
(`src/support.py`, `src/flows.py::support_flow`) has node set
$\Sigma_{\ge2}(d)$ and edges = the cover moves that stay inside it: split a
part $n_i\ge4$ into $(p,\,n_i-p)$ with $2\le p\le n_i-2$ (adding the element
$j=j_{i-1}+p$), plus the same source/sink attachments and
$\mathrm{INF}=S+1$.

**Proposition 3.** $\max\text{flow}(G)=\max\text{flow}(H)$.

*Proof.* ($\ge$) $H$'s edge set embeds into $G$'s (each split is a cover
edge), so any $H$-flow is a $G$-flow of the same value.

($\le$) Decompose a maximum flow of $G$ into $s$–$t$ paths (the lattice part
of $G$ is a DAG, so path decomposition with no cycles applies). Each path is
$s\to J_0\lessdot J_1\lessdot\cdots\lessdot J_r\to t$ with $J_0\in P$,
$J_r\in N$, hence $J_0\subseteq J_r$ and **both endpoints lie in
$\Sigma_{\ge2}$** (nonzero weight). Claim: $J_r$ is reachable from $J_0$
inside $H$. Indeed $\operatorname{comp}(J_r)$ refines
$\operatorname{comp}(J_0)$ blockwise: block $n_i$ splits into consecutive
parts $(m_{i,1},\dots,m_{i,\ell_i})$, all $\ge2$. Peel parts off from the
left: the step splitting $m_{i,k}+\cdots+m_{i,\ell_i}$ into
$\big(m_{i,k},\ m_{i,k+1}+\cdots+m_{i,\ell_i}\big)$ has both pieces $\ge2$
whenever $k<\ell_i$, so every intermediate composition stays in
$\Sigma_{\ge2}$ and every step is an $H$-edge. Reroute each path's value along
such an $H$-path from $J_0$ to $J_r$; interior capacities $\mathrm{INF}$ are
never exceeded because the total rerouted value is $\le S<\mathrm{INF}$.
This produces an $H$-flow of the same value. ∎

Consequently feasibility, deficits, and (via (cut=ideal) applied to the induced
subposet, whose ideals are exactly $\{\mathcal D\cap\Sigma_{\ge2}\}$ and whose
weight sums agree with those of their downward closures in $2^{[d]}$ since all
added nodes have $w=0$) minimum negative ideals can all be computed on $H$.
The connectivity fact "reachable in $H$ ⟺ contained as subsets" is also
machine-checked exhaustively for $2\le d\le5$
(`tests/test_support.py::test_split_dag_reachability_equals_containment`).

## 5. Hand calculations ($d=1,2,3$) — pinned in tests

| $d$ | $J$ | comp | $U_J$ | $a_J$ | $w_J$ |
|---|---|---|---|---|---|
| 1 | $\varnothing$ | (3) | 1 | 0 | 0 |
| 1 | $\{1\}$ | (1,2) | 2 | 0 | 0 |
| 2 | $\varnothing$ | (4) | 1 | 6 | 6 |
| 2 | $\{2\}$ | (2,2) | 3 | $-2$ | $-6$ |
| 3 | $\varnothing$ | (5) | 1 | 20 | 20 |
| 3 | $\{2\}$ | (2,3) | 6 | $-2$ | $-12$ |
| 3 | $\{3\}$ | (3,2) | 4 | $-2$ | $-8$ |

(All omitted $J$ have a part equal to 1, hence $w_J=0$.) Each row was computed
by hand from the definitions and is asserted verbatim in
`tests/test_weights.py::test_hand_calculations`. Note $\sum w=0$ in each row
block, and the flows $\varnothing\to\{2\}$ ($d=2$), resp.
$\varnothing\to\{2\},\varnothing\to\{3\}$ ($d=3$), realize the certificates.

## 6. Review of the proofs against the implemented network and oracle

* `src/flows.py::full_lattice_flow` builds exactly $G$ of Section 3.2
  (source cap $w_J$ on $P$, sink cap $-w_J$ on $N$, all cover edges upward at
  $\mathrm{INF}=S+1$). `support_flow` builds $H$ of Section 4.
* `src/ideals.py` enumerates **all** ideals for $d\le5$ (counts match the
  Dedekind numbers $3,6,20,168,7581$, an independent check of the enumerator)
  and minimises $\sum_{\mathcal D}w$.
* `tests/test_flows_small.py::test_ideal_oracle_vs_flows` asserts, for
  $d\le 5$, the exact relation of Section 3.4:
  $\text{deficit}=-\min_{\mathcal D}\sum_{\mathcal D}w$ on **both** networks,
  and feasibility ⟺ the minimum is $0$. This is the empirical counterpart of
  Propositions 2 and 3 and passes exactly (values $S=0,6,20,90,840$ for
  $d=1..5$, all feasible).
* `tests/test_flows_small.py::test_flow_conservation_and_divergence` recovers
  $f$ from the solved network and asserts $\operatorname{div}f=w_J$ at every
  support node — the certificate property of Proposition 1/Claim A.

## 7. Experiment log

* 2026-08-10 — Stage 1 complete (commit `4f0b233`): dual weight
  implementations agree ($d\le5$); integrality, $\sum w=0$, hand values;
  ideal oracle vs both max-flow networks agree, all feasible, $d\le5$.
* 2026-08-10 — Equivalence proofs written (this file, Sections 2–4) and
  reviewed against code; all tests re-run.
* 2026-08-10 — Stage 2: support-DAG max-flow **FEASIBLE for every
  $d=1,\dots,25$** (exact big-int Dinic; per-$d$ JSON in `results/`).
  Reproduces the paper's $d\le19$ (Remark 3.31) and extends to $d\le25$.
  Sizes at $d=25$: 121393 nodes, 823800 split edges, supply $S$ of 90 bits,
  63 s, 333 MiB. $\sum_J w_J=0$ checked exactly for all these $d$.
  Note: $S$ exceeds 63 bits from $d=18$ on, so exact big-integer capacities
  are not optional — an int64 max-flow library would silently overflow.

## Failed ideas

*(none recorded yet — the section is kept so that dead ends get logged here.)*
