# A proof of Cheng–Lin Conjecture 3.30

**Status.** Complete symbolic proof of Conjecture 3.30 of R. Cheng and
W. Lin, arXiv:2603.21680**v3** (pinned copy `paper/cheng-lin-v3.pdf`), for
every $d\ge1$. The certificate formula was proposed externally; every step
below was independently re-derived in this repository (audit trail:
`results/audit_explicit_certificate.json`, `src/run_audit_explicit.py`,
`tests/test_explicit_certificate.py`) and machine-corroborated in exact
integer arithmetic for $d\le25$. The proof itself is uniform in $d$ and does
not rely on the computations. It awaits external human review.

---

## 1. Setting and statement

Fix $d\ge1$. For $J=\{j_1<\cdots<j_m\}\subseteq[d]$ set $j_0=0$ and let

$$n_i=j_i-j_{i-1}\ (1\le i\le m),\qquad n_{m+1}=d+2-j_m,$$

a composition of $d+2$ with $n_{m+1}\ge2$. Define

$$U_J=\frac{n_{m+1}(d+1)!}{\prod_{i=1}^{m+1}n_i!},\qquad
a_J=\prod_{i=1}^{m+1}(n_i-1)\cdot\frac12\sum_{i=1}^{m+1}n_i(n_i-3).$$

For a matroid $M$ of rank $d+1$, $N_J=N_J(M)$ denotes the number of flags of
flats of rank type $J$. Lemma 3.29 of the paper states the monotonicity
inequalities

$$\frac{N_J}{U_J}\le\frac{N_{J'}}{U_{J'}}\qquad(J\subseteq J'). \tag{M}$$

**Conjecture 3.30 (Cheng–Lin).** The inequality
$\sum_{J\subseteq[d]}a_JN_J\le0$ of Corollary 3.28 is a nonnegative linear
combination of the inequalities (M): there exist $\lambda_{(J,J')}\ge0$ with

$$\sum_{J\subseteq[d]}a_JN_J=\sum_{J\subsetneq J'}\lambda_{(J,J')}
\Big(\frac{N_J}{U_J}-\frac{N_{J'}}{U_{J'}}\Big)
\quad\text{identically as linear forms in }(N_K)_{K\subseteq[d]}. \tag{3.30}$$

**Theorem.** Conjecture 3.30 holds for every $d\ge1$, with the explicit
coefficients of Section 3.

## 2. Reduction to a divergence problem

Write $w_J=U_Ja_J$ and $x_J=N_J/U_J$. Substituting $N_J=U_Jx_J$, (3.30) is
equivalent to $\sum_Jw_Jx_J=\sum\lambda_{(J,J')}(x_J-x_{J'})$ identically,
i.e., comparing coefficients of $x_K$, to: $\lambda$ is a nonnegative flow
on the DAG of nested pairs with divergence

$$\operatorname{outflow}(K)-\operatorname{inflow}(K)=w_K\quad\text{for all }K. \tag{D}$$

Since the inequality (M) for any nested pair telescopes along a saturated
chain of *cover* pairs $J\lessdot J\cup\{j\}$, a nonnegative flow on cover
edges with divergence (D) yields (3.30) directly (put $\lambda=f$ on covers,
$0$ elsewhere). It therefore suffices to construct

$$f\ \ge 0\ \text{on the cover edges } J\to J\cup\{j\},\qquad
\operatorname{div}f=w. \tag{$\ast$}$$

(Full details of this reduction, including the sign audit and the converse,
are in `RESEARCH_NOTES.md`, Proposition 1; only the easy direction just
stated is needed here.)

We use composition language: $J\leftrightarrow$ its composition; a cover
step $J\to J\cup\{j\}$ splits one block $n_i$ into $(p,\,n_i-p)$, $1\le
p\le n_i-1$, where $j=j_{i-1}+p$. Call $J$ (and its composition) a *support
node* if all parts are $\ge2$; since $a_J$ contains $\prod(n_i-1)$, $w_J=0$
off the support.

## 3. The certificate

For a support composition $c=(n_1,\dots,n_r)$ of $d+2$ define

$$G(c)=U_c\prod_{i=1}^r(n_i-1)
=(d+1)!\;n_r\prod_{i=1}^r\frac{n_i-1}{n_i!}\;>\;0,
\qquad \rho(n)=\frac{n(n-3)}{2},$$

so that, directly from the definitions,

$$w(c)=G(c)\sum_{i=1}^r\rho(n_i). \tag{W}$$

Note $\rho(2)=-1$, $\rho(3)=0$, $\rho(n)>0$ for $n\ge4$.

**Selected peel moves.** For each support composition $c=(n_1,\dots,n_r)$:

* **(N)** for every *nonfinal* block $n_i\ge4$ ($i<r$): the single cover
  edge splitting $n_i\to(2,\,n_i-2)$, with flow $G(\text{child})$;
* **(FL)** if the *final* block $n_r\ge4$: the cover edge
  $n_r\to(2,\,n_r-2)$, with flow $G(\text{child})$;
* **(FR)** if $n_r\ge4$: the cover edge $n_r\to(n_r-2,\,2)$, with flow
  $G(\text{child})$.

For $n_r=4$ the moves (FL) and (FR) are the *same* cover edge (splitting
$4\to(2,2)$ adds the same element); its flow is the sum $2G(\text{child})$.
All other selected moves are pairwise distinct edges. Every selected edge
joins support nodes (both parts $2$ and $n_i-2$ are $\ge2$), and

$$f\ :=\ \sum_{\text{selected moves}}G(\text{child})\cdot
\mathbf 1_{\text{edge}}\ \ge\ 0,$$

zero on all cover edges not selected. Positivity is manifest: $G>0$.

## 4. Two lemmas

**Lemma 1 (ratio identities).** Let $c$ be a support composition, $m\ge4$ a
block of $c$, and $c'$ the child of the indicated move. Then

$$\frac{G(c')}{G(c)}=
\begin{cases}
\rho(m)=\dfrac{m(m-3)}{2}, & \text{(N), $m$ nonfinal},\\[2mm]
\dfrac{(m-2)(m-3)}{2}, & \text{(FL), $m$ final},\\[2mm]
m-3, & \text{(FR), $m$ final},
\end{cases}
\qquad\text{and}\qquad
\frac{(m-2)(m-3)}{2}+(m-3)=\rho(m).$$

*Proof.* Write $G(c)=(d+1)!\,n_r\prod_i\frac{n_i-1}{n_i!}$. All factors
associated with unaffected blocks cancel in $G(c')/G(c)$.

(N): the last part is unchanged; the factor $\frac{m-1}{m!}$ is replaced by
$\frac{2-1}{2!}\cdot\frac{m-3}{(m-2)!}$. Hence the ratio is
$\frac{m!}{2\,(m-2)!}\cdot\frac{m-3}{m-1}
=\frac{m(m-1)}{2}\cdot\frac{m-3}{m-1}=\frac{m(m-3)}{2}$.

(FL): in addition to the same block replacement, the last-part prefactor
changes from $m$ to $m-2$; the ratio acquires the extra factor
$\frac{m-2}{m}$, giving $\frac{(m-2)(m-3)}{2}$.

(FR): the factor $\frac{m-1}{m!}$ is replaced by
$\frac{m-3}{(m-2)!}\cdot\frac{1}{2!}$ and the last-part prefactor changes
from $m$ to $2$: ratio $=\frac{2}{m}\cdot\frac{m!}{2\,(m-2)!}\cdot
\frac{m-3}{m-1}=(m-1)\cdot\frac{m-3}{m-1}=m-3$.

The final identity is $(m-3)\big(\frac{m-2}{2}+1\big)=\frac{m(m-3)}{2}$. $\blacksquare$

**Lemma 2 (in-edges).** Let $c=(c_1,\dots,c_r)$ be a support composition.
The selected moves with child $c$ are exactly the following, one for each
index $i$ with $c_i=2$ (so their number, with multiplicity, is the number of
$2$-blocks of $c$), and each carries flow $G(c)$:

* $c_i=2$ with $i\le r-2$: the (N)-move of the parent obtained by merging
  $c_i,c_{i+1}$ into the nonfinal block $2+c_{i+1}\ge4$;
* $c_{r-1}=2$: the (FL)-move of the parent obtained by merging
  $c_{r-1},c_r$ into the final block $2+c_r\ge4$;
* $c_r=2$: the (FR)-move of the parent obtained by merging $c_{r-1},c_r$
  into the final block $c_{r-1}+2\ge4$.

*Proof.* Each selected move inserts the pattern of its type, so its child
determines the move: an (N)-move creates a block equal to $2$ at a position
$i$ of the child with at least two blocks after it ($i\le r-2$; in the
parent the merged block sits at a nonfinal index), and the parent is
recovered by merging that $2$ with its right neighbour. Conversely, for any
$i\le r-2$ with $c_i=2$, merging produces a support composition whose block
$2+c_{i+1}\ge4$ is nonfinal, so its (N)-move is selected and returns $c$.
The correspondence is bijective for these positions. An (FL)-move creates a
$2$ exactly at position $r-1$ of its child; merging $c_{r-1}=2$ with the
final block recovers the unique such parent, whose final block $2+c_r\ge4$
indeed has a selected (FL)-move returning $c$. An (FR)-move creates a final
$2$; merging the last two blocks recovers the unique parent, final block
$c_{r-1}+2\ge4$, whose (FR)-move returns $c$. No other selected move can
have child $c$.

Multiplicity: the parents for the three cases are distinct edges except
when $c_{r-1}=c_r=2$, where the (FL)- and (FR)-parents coincide (final
block $4$, the coincident-edge case of Section 3); there the single edge
carries $2G(c)$, matching the two $2$-blocks at positions $r-1,r$. Every
selected move has flow $G(\text{child})=G(c)$ by definition.

Degenerate cases: if $r=1$ there is no $2$-block for $d\ge1$ (the single
block is $d+2\ge3$) and indeed no selected move has a one-block child. Runs
of consecutive $2$'s at positions $i,i+1\le r-2$ produce *different*
parents (merging at $i$ versus $i+1$), so there is no further coincidence.
Blocks equal to $3$ receive nothing. Compositions containing a part $1$
are neither sources nor targets of selected moves, since parents (merges)
and children (peels with both pieces $\ge2$) of support nodes are support
nodes. $\blacksquare$

## 5. Proof of the Theorem

Let $c$ be any support composition. By Section 3 and Lemma 1,

$$\operatorname{outflow}(c)
=\sum_{\substack{i<r\\ c_i\ge4}}G(c)\,\rho(c_i)
+\mathbf 1_{c_r\ge4}\,G(c)\Big(\tfrac{(c_r-2)(c_r-3)}{2}+(c_r-3)\Big)
=G(c)\sum_{c_i\ge4}\rho(c_i).$$

By Lemma 2,
$\operatorname{inflow}(c)=\#\{i:c_i=2\}\cdot G(c)=-G(c)\sum_{c_i=2}\rho(c_i)$
(as $\rho(2)=-1$). Since $\rho(3)=0$ and $\rho(c_i)=0$ contributes nothing,

$$\operatorname{div}f(c)=G(c)\sum_{i=1}^r\rho(c_i)\overset{\text{(W)}}{=}w(c).$$

At every non-support node no selected edge is incident (Lemma 2, last
paragraph), so $\operatorname{div}f=0=w$ there. Thus $f$ satisfies $(\ast)$:
it is a nonnegative flow on Boolean cover edges with divergence $w$, and by
Section 2 Conjecture 3.30 holds, with explicit coefficients

$$\lambda_{\big(J,\;J\cup\{j\}\big)}\;=\;
\sum_{\substack{\text{selected moves of }c(J)\\ \text{adding the element }j}}
G\big(c(J\cup\{j\})\big)
\;=\;
\begin{cases}
G(c'), & \text{move (N) or a single final peel},\\
2\,G(c'), & \text{final block }4\text{ split to }(2,2),\\
0, & \text{all other pairs},
\end{cases}$$

where $c'$ is the composition of $J\cup\{j\}$. $\blacksquare$

**Remark (verification).** The divergence identity, positivity, and the
peel2 support of $f$ were verified in exact integer arithmetic for every
support node at every $d\le25$ (121393 nodes, 364057 edges at $d=25$), and
over *all* $2^d$ subsets for $d\le10$; the ratio identities of Lemma 1 were
verified for $m\le200$ in varied contexts
(`results/audit_explicit_certificate.json`). The certificate is supported
on peel-2 splits only, explaining the Stage 3 observation that the
peel2-restricted network stays feasible.

## 6. Corollaries: the Stage 3 empirical structure becomes theorems

**Corollary 1 (staircase identities, all $d$).** For
$T_k=\{2,4,\dots,2k\}\cup\{2k+1,\dots,d\}$, $0\le k\le\lfloor d/2\rfloor$:
$\displaystyle\sigma(T_k):=\sum_{J\subseteq T_k}w_J=0.$

*Proof.* Let $D_k=\{J:J\subseteq T_k\}=\{J:\text{every element}\le2k
\text{ of }J\text{ is even}\}$, a downward-closed ideal. Cover edges point
upward, so no edge enters $D_k$ from outside; summing
$\operatorname{div}f=w$ over $D_k$ gives
$\sigma(T_k)=\sum_{e\text{ leaving }D_k}f(e)$. We claim no *selected* edge
leaves $D_k$. A selected move adds the element $j=\pi+2$ (moves (N), (FL),
where $\pi$ is the prefix sum before the split block) or $j=d$ (move (FR),
since the new cut precedes a final part $2$). If $j$ is odd and $j\le
2k$: in the first case $\pi=j-2$ is odd and positive, so $\pi$ is an
element of $J$ smaller than $2k$ and odd, whence $J\notin D_k$ already; in
the second case $j=d\ge2k+1$ for $k\le\lfloor d/2\rfloor$ when $d$ is odd,
and $j=d$ is even when $d$ is even — never an odd $j\le2k$. So every edge
leaving $D_k$ has $f(e)=0$, and $\sigma(T_k)=0$. $\blacksquare$

**Corollary 2 (shell decomposition, all $d$).** In *every* nonnegative
flow $f'$ with $\operatorname{div}f'=w$ (not only the explicit one), each
edge crossing some $\partial D_k$ carries zero flow; hence every
certificate decomposes into independent flows on the shells
$D_{k-1}\setminus D_k$ (subsets classified by their smallest odd element,
with the residual class for $\ge2\lfloor d/2\rfloor+1$).

*Proof.* By Corollary 1, $\sum_{J\in D_k}w_J=0$; summing
$\operatorname{div}f'=w$ over the ideal $D_k$ and using that no edge enters
an ideal, $0=\sum_{e\text{ leaving }D_k}f'(e)$ with all terms $\ge0$.
$\blacksquare$

(The further Stage 3 observation that the staircases are the *only* tight
principal ideals remains empirical, verified $d\le14$; it is not needed
anywhere.)

## 7. What this rests on

* The pinned definitions of $U_J,a_J$ from arXiv:2603.21680v3 (§3.4) and
  the identity-of-linear-forms reading of "nonnegative linear combination"
  (RESEARCH_NOTES.md §1); under this reading the theorem resolves the
  conjecture affirmatively for all $d\ge1$ and hence, via Lemma 3.29,
  reproves Corollary 3.28 for all matroids.
* Elementary manipulations of factorials (Lemma 1) and a finite case
  analysis (Lemma 2) — no computer assistance is required by the proof;
  the $d\le25$ verification is corroboration only.
* Provenance: the candidate formula was supplied externally; this
  repository's contribution is the independent audit, the bijection proof,
  the machine corroboration, and the corollaries. External human review is
  still warranted before public claims.
