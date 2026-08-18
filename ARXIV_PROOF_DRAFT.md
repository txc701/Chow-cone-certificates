# An explicit certificate for Conjecture 3.30 of Cheng–Lin

*Referee-facing standalone draft. Mathematical content frozen at repository
commit `e0e64a3`; source of truth `PROOF_CONJECTURE_3_30.md`. This text is
self-contained: no code, computation, or repository artifact is needed to
verify it.*

## 1. Statement

Throughout, $d\ge1$ is an integer and $[d]=\{1,\dots,d\}$. We use the
notation of Cheng–Lin, arXiv:2603.21680v3, §3.4. For a subset
$J=\{j_1<\cdots<j_m\}\subseteq[d]$ (possibly empty, $m=0$) set $j_0=0$ and

$$n_i=j_i-j_{i-1}\quad(1\le i\le m),\qquad n_{m+1}=d+2-j_m,$$

so that $(n_1,\dots,n_{m+1})$ is a composition of $d+2$ into $m+1$ positive
parts with $n_{m+1}\ge2$ (because $j_m\le d$). Define

$$U_J:=\frac{n_{m+1}\,(d+1)!}{\prod_{i=1}^{m+1}n_i!},\qquad
a_J:=\prod_{i=1}^{m+1}(n_i-1)\cdot\left(\frac12\sum_{i=1}^{m+1}n_i(n_i-3)\right).$$

For a matroid $M$ of rank $d+1$, $N_J=N_J(M)$ denotes the number of flags
of flats of $M$ of rank type $J$; Cheng–Lin's Lemma 3.29 states that

$$\frac{N_J}{U_J}\ \le\ \frac{N_{J'}}{U_{J'}}
\qquad\text{whenever } J\subseteq J'\subseteq[d]. \tag{M$_{J,J'}$}$$

(The smaller set gives the smaller normalized flag count; $U_J>0$ for all
$J$.) Corollary 3.28 of Cheng–Lin asserts
$\sum_{J\subseteq[d]}a_JN_J\le0$, and their Conjecture 3.30 asserts that
this inequality is a nonnegative linear combination of the inequalities
(M$_{J,J'}$). We prove:

**Theorem 1.** For every $d\ge1$ there exist real numbers
$\lambda_{(J,J')}\ge0$, indexed by the pairs $J\subsetneq J'\subseteq[d]$,
such that

$$\sum_{J\subseteq[d]}a_J\,N_J\;=\;\sum_{J\subsetneq J'}
\lambda_{(J,J')}\left(\frac{N_J}{U_J}-\frac{N_{J'}}{U_{J'}}\right)
\tag{1}$$

holds identically as an equality of linear forms in the variables
$(N_K)_{K\subseteq[d]}$. In particular Conjecture 3.30 holds for every
$d\ge1$. The coefficients are explicit (Definition 4 and Theorem 1$'$
below), and are nonzero only on cover pairs $J'=J\cup\{j\}$.

Two remarks on the reading of the statement. First, (1) with
$\lambda\ge0$ exhibits $\sum a_JN_J\le0$ as a consequence of the
inequalities (M$_{J,J'}$), which is the meaning of "nonnegative linear
combination"; scaling any single inequality by a positive constant is
absorbed into $\lambda$, so the choice of normalization of (M$_{J,J'}$) is
immaterial. Second, whether the sum in Corollary 3.28 is over all
$J\subseteq[d]$ or only proper subsets is also immaterial: for $J=[d]$
the composition is $(1,1,\dots,1,2)$ for $d\ge2$ (resp. $(1,2)$ for
$d=1$), which contains a part equal to $1$, so $a_{[d]}=0$ and the term
vanishes (see Lemma 1 below).

## 2. Composition notation and the cover-edge dictionary

We write $c(J)=(n_1,\dots,n_r)$, $r=m+1$, for the composition associated
with $J$ as above. The map $J\mapsto c(J)$ is a bijection from subsets of
$[d]$ onto compositions of $d+2$ whose last part is $\ge2$; the inverse
recovers $J$ as the set of proper prefix sums
$j_i=n_1+\cdots+n_i$, $1\le i\le r-1$. Blocks are indexed $1$-based; we
call block $r$ the *final* block and blocks $1,\dots,r-1$ *nonfinal*. The
*prefix sum before block $i$* is $\pi_i:=n_1+\cdots+n_{i-1}=j_{i-1}$
(so $\pi_1=0$).

**Lemma 1 (support).** If some part of $c(J)$ equals $1$, then $a_J=0$.
Consequently $w_J:=U_Ja_J$ vanishes unless all parts of $c(J)$ are
$\ge2$; we call such $J$ (and such compositions) *support* elements. In
terms of $J$: support means $1\notin J$ and $J$ contains no two consecutive
integers.

*Proof.* The factor $\prod_i(n_i-1)$ vanishes. For the last sentence:
$n_1=j_1=1$ iff $1\in J$; $n_{i}=j_i-j_{i-1}=1$ (for $2\le i\le m$) iff
$j_{i-1},j_i$ are consecutive; $n_{m+1}\ge2$ always. $\square$

**Cover-edge dictionary.** For $J\subseteq[d]$ and $j\in[d]\setminus J$,
the Boolean cover relation $J\lessdot J\cup\{j\}$ acts on compositions as
follows. Let $i$ be the unique index with $\pi_i<j<\pi_i+n_i$ if $i<r$,
resp. $\pi_r<j\le d$ if $i=r$, and put $p:=j-\pi_i$. Then
$c(J\cup\{j\})$ is obtained from $c(J)$ by replacing block $n_i$ with the
pair $(p,\,n_i-p)$. The admissible offsets are

$$p\in\{1,\dots,n_i-1\}\ \text{ for } i<r,\qquad
p\in\{1,\dots,n_r-2\}\ \text{ for } i=r,$$

the final-block bound being $p=j-\pi_r\le d-\pi_r=n_r-2$: an offset
$p=n_r-1$ would require the element $j=d+1\notin[d]$. Conversely each
admissible $(i,p)$ arises from exactly one $j$; we may therefore speak
interchangeably of the cover edge $(J,J\cup\{j\})$ and of *the split of
block $i$ of $c(J)$ at offset $p$*. Note that both blocks of the resulting
pair are nonempty, and the last part of the child is
$n_r-p\ge2$ when $i=r$ (by the bound above) and $n_r$ (unchanged) when
$i<r$, so the child is again a composition of the required shape.

## 3. Reduction to a divergence identity

Orient every cover edge upward, from $J$ to $J\cup\{j\}$. A *flow* is a
function $f\ge0$ on the set of cover edges; its *divergence* at $K$ is

$$\operatorname{div}f(K):=
\underbrace{\sum_{j\notin K}f\big(K\to K\cup\{j\}\big)}_{\text{outflow}(K)}
\;-\;
\underbrace{\sum_{j\in K}f\big(K\setminus\{j\}\to K\big)}_{\text{inflow}(K)}.$$

**Lemma 2 (reduction).** Suppose $f\ge0$ is a flow on cover edges with

$$\operatorname{div}f(K)=w_K\quad\text{for every }K\subseteq[d].
\tag{D}$$

Then (1) holds with $\lambda_{(J,J\cup\{j\})}=f(J\to J\cup\{j\})$ and
$\lambda_{(J,J')}=0$ when $J'$ is not a cover of $J$; hence Theorem 1
follows from the existence of such an $f$.

*Proof.* Cover pairs are nested pairs, so the right side of (1) with these
$\lambda$ is
$\sum_{\text{cover edges }e=(K\to K')}f(e)\big(\frac{N_K}{U_K}-\frac{N_{K'}}{U_{K'}}\big)$.
Fix $K\subseteq[d]$ and compare coefficients of the variable $N_K$ on both
sides of (1). On the right, $N_K$ appears with coefficient $+f(e)/U_K$ for
each edge $e$ leaving $K$ and $-f(e)/U_K$ for each edge $e$ entering $K$;
the total is $\operatorname{div}f(K)/U_K$. On the left the coefficient is
$a_K=w_K/U_K$. By (D) these agree for every $K$, which is precisely the
asserted identity of linear forms. Nonnegativity of $\lambda$ is
nonnegativity of $f$. $\square$

The sign orientation deserves one explicit check: in (1) the bracket is
$\frac{N_J}{U_J}-\frac{N_{J'}}{U_{J'}}$ with $J\subsetneq J'$, which is
$\le0$ by (M$_{J,J'}$); thus (1) with $\lambda\ge0$ indeed *proves*
$\sum a_JN_J\le0$. Correspondingly (D) makes sets with $w_K>0$ *sources*
(net outflow) and sets with $w_K<0$ *sinks*, and flow runs upward, from
coarser toward finer compositions.

It remains to construct $f$. This occupies the rest of the paper.

## 4. The certificate

**Definition 3.** For a support composition $c=(n_1,\dots,n_r)$ of $d+2$
put

$$G(c):=U_c\prod_{i=1}^r(n_i-1)
=(d+1)!\;n_r\;\prod_{i=1}^r\frac{n_i-1}{n_i!}\;>\;0,
\qquad
\rho(n):=\frac{n(n-3)}{2},$$

where $U_c$ denotes $U_J$ for the subset $J$ with $c(J)=c$. Note
$\rho(2)=-1$, $\rho(3)=0$, and $\rho(n)>0$ for $n\ge4$. Directly from the
definitions of $U_J$ and $a_J$,

$$w(c)\,:=\,U_c\,a_c\,=\,G(c)\sum_{i=1}^r\rho(n_i). \tag{W}$$

**Definition 4 (selected moves and the flow $f$).** Let
$c=(n_1,\dots,n_r)$ be a support composition. Its *selected moves* are:

* **(N)** for each nonfinal index $i<r$ with $n_i\ge4$: the split of block
  $i$ at offset $p=2$, i.e. $n_i\to(2,\,n_i-2)$;
* **(FL)** if $n_r\ge4$: the split of block $r$ at offset $p=2$, i.e.
  $n_r\to(2,\,n_r-2)$;
* **(FR)** if $n_r\ge4$: the split of block $r$ at offset $p=n_r-2$, i.e.
  $n_r\to(n_r-2,\,2)$.

All these offsets are admissible in the sense of Section 2: for (N),
$p=2\in\{1,\dots,n_i-1\}$ because $n_i\ge4$; for (FL) and (FR),
$p\in\{2,\,n_r-2\}\subseteq\{1,\dots,n_r-2\}$ because $n_r\ge4$; in
particular the element added by (FR) is
$j=\pi_r+n_r-2=(d+2)-2=d\in[d]$. Both parts produced by any selected
move are $\ge2$, so the child of a selected move is again a support
composition. Each selected move is assigned the *move-flow*
$G(\text{child})$, where child denotes the resulting composition.

The moves (FL) and (FR) coincide as cover edges precisely when
$n_r=4$ (then $p=2=n_r-2$, one and the same added element); for
$n_r\ge5$ they are distinct edges. Define the flow $f$ on Boolean cover
edges by

$$f(e):=\sum_{\substack{\text{selected moves realizing}\\ \text{the cover edge }e}}
G(\text{child of the move}),$$

and $f(e)=0$ for edges realized by no selected move. Thus $f\ge0$; on the
coincident edge of a final block $4$ the value is $2\,G(\text{child})$,
and on every other selected edge it is $G(\text{child})$.

We must show (D): $\operatorname{div}f=w$ at every $K\subseteq[d]$.

## 5. Outgoing flow

**Lemma 5 (ratios).** Let $c=(n_1,\dots,n_r)$ be a support composition
and $m=n_i\ge4$ a block. Let $c'$ denote the child of the indicated
selected move at block $i$. Then

$$\frac{G(c')}{G(c)}=
\begin{cases}
\dfrac{m(m-3)}{2}=\rho(m), & \text{(N): }i<r,\ m\to(2,m-2),\\[2mm]
\dfrac{(m-2)(m-3)}{2}, & \text{(FL): }i=r,\ m\to(2,m-2),\\[2mm]
m-3, & \text{(FR): }i=r,\ m\to(m-2,2),
\end{cases}$$

and $\dfrac{(m-2)(m-3)}{2}+(m-3)=\rho(m)$.

*Proof.* Use $G(c)=(d+1)!\,n_r\prod_{i=1}^r\frac{n_i-1}{n_i!}$. In each
ratio the factor $(d+1)!$ and the factors of all unaffected blocks cancel.

(N): the last block is not the one split, so the prefactor $n_r$ also
cancels, and the block factor $\frac{m-1}{m!}$ is replaced by the two
factors $\frac{2-1}{2!}\cdot\frac{(m-2)-1}{(m-2)!}
=\frac12\cdot\frac{m-3}{(m-2)!}$. Hence

$$\frac{G(c')}{G(c)}
=\frac{\tfrac12\cdot\tfrac{m-3}{(m-2)!}}{\tfrac{m-1}{m!}}
=\frac{m!}{2\,(m-2)!}\cdot\frac{m-3}{m-1}
=\frac{m(m-1)}{2}\cdot\frac{m-3}{m-1}
=\frac{m(m-3)}{2}.$$

(FL): the block replacement is as in (N), and additionally the last part
changes from $m$ to $m-2$, so the prefactor contributes $\frac{m-2}{m}$:

$$\frac{G(c')}{G(c)}
=\frac{m-2}{m}\cdot\frac{m(m-3)}{2}
=\frac{(m-2)(m-3)}{2}.$$

(FR): the block factor $\frac{m-1}{m!}$ is replaced by
$\frac{m-3}{(m-2)!}\cdot\frac{2-1}{2!}$ and the last-part prefactor
changes from $m$ to $2$:

$$\frac{G(c')}{G(c)}
=\frac{2}{m}\cdot\frac{\tfrac{m-3}{(m-2)!}\cdot\tfrac12}{\tfrac{m-1}{m!}}
=\frac{2}{m}\cdot\frac{m!}{2\,(m-2)!}\cdot\frac{m-3}{m-1}
=\frac{2}{m}\cdot\frac{m(m-1)}{2}\cdot\frac{m-3}{m-1}
=m-3.$$

Finally $(m-3)\big(\frac{m-2}{2}+1\big)=(m-3)\cdot\frac{m}{2}=\rho(m)$.
$\square$

**Corollary 6 (total outflow).** For every support composition $c$,

$$\operatorname{outflow}(c)
=\sum_{\text{selected moves of }c}G(\text{child})
=G(c)\sum_{i:\;n_i\ge4}\rho(n_i).$$

*Proof.* Outflow is the sum of $f$ over edges leaving $c$; by Definition 4
this equals the sum of move-flows over all selected moves of $c$ (the
coincident final-$4$ edge carries the sum of its two move-flows, so the
edge-sum and the move-sum agree). By Lemma 5 the move-flows are:
$G(c)\rho(n_i)$ for each nonfinal $n_i\ge4$; and, if $n_r\ge4$,
$G(c)\frac{(n_r-2)(n_r-3)}{2}+G(c)(n_r-3)=G(c)\rho(n_r)$ for the final
block. Blocks with $n_i\in\{2,3\}$ admit no selected move. $\square$

## 6. Incoming flow

This is the heart of the bookkeeping. Fix a support composition
$c=(c_1,\dots,c_r)$ of $d+2$; we determine *every* selected move (of every
possible parent) whose child is $c$.

**Definition.** If a selected move splits block $i$ of its parent, its
child contains the *created $2$*: the part equal to $2$ that the move
inserts. Its position in the child is:

* for (N) at parent index $i$ (parent has $s$ blocks, $i\le s-1$):
  position $i$ of the child, which has $r=s+1$ blocks; thus
  $i\le s-1=r-2$, i.e. **the created $2$ of an (N)-move lies at a
  position $\le r-2$ of its child**;
* for (FL) (split of the final block $s$ of the parent): position
  $s=r-1$ of the child;
* for (FR): position $s+1=r$ (final position) of the child.

The three position ranges $\{1,\dots,r-2\}$, $\{r-1\}$, $\{r\}$ are
pairwise disjoint, so **the position of the created $2$ determines the
type of the move**, and (as we verify next) the parent as well.

**Lemma 7 (in-edges).** Let $c=(c_1,\dots,c_r)$ be a support composition.
The selected moves with child $c$ are in bijection with the set
$\{i:\ c_i=2\}$ of positions of $2$-blocks of $c$, via the position of the
created $2$. Explicitly, for each $i$ with $c_i=2$ the corresponding move
and parent are:

* $i\le r-2$: the (N)-move of the parent
  $p=(c_1,\dots,c_{i-1},\,2+c_{i+1},\,c_{i+2},\dots,c_r)$
  at its (nonfinal) index $i$;
* $i=r-1$: the (FL)-move of the parent
  $p=(c_1,\dots,c_{r-2},\,2+c_r)$;
* $i=r$: the (FR)-move of the parent
  $p=(c_1,\dots,c_{r-2},\,c_{r-1}+2)$.

Each of these moves has move-flow exactly $G(c)$. Moreover, distinct
moves in this list define distinct Boolean cover edges into $c$, with a
single exception: if $c_{r-1}=c_r=2$, the moves for $i=r-1$ and $i=r$ have
the same parent $p=(c_1,\dots,c_{r-2},4)$ and realize the same cover edge
(the (FL)/(FR) coincidence of Definition 4 for final block $4$).
Consequently

$$\operatorname{inflow}(c)\;=\;\#\{i:\ c_i=2\}\cdot G(c),$$

where in the exceptional case the single coincident edge contributes its
flow $2G(c)$, accounting for both positions $r-1$ and $r$.

*Proof.* We prove: (completeness) every selected move with child $c$
appears in the list; (well-definedness) every entry of the list is a
selected move of a support parent with child $c$; (injectivity) distinct
positions give distinct moves; (aliasing) distinct moves give distinct
cover edges except in the stated case; (flow) each move-flow is $G(c)$.

*Completeness.* Let a selected move of a parent $p$ have child $c$. By the
Definition above, its created $2$ sits at a position $i$ of $c$ with
$c_i=2$, and the type of the move is (N) if $i\le r-2$, (FL) if $i=r-1$,
(FR) if $i=r$. In each case the parent is recovered from $c$ and $i$ by
reversing the split, i.e. by merging: for (N) and (FL), the move replaced
a parent block by the pair (created $2$, following block), so
$p$ is obtained from $c$ by replacing the pair $(c_i,c_{i+1})=(2,c_{i+1})$
by the single block $2+c_{i+1}$; for (FR), the move replaced the parent's
final block by the pair $(c_{r-1},2)$, so $p$ is obtained by replacing
$(c_{r-1},c_r)=(c_{r-1},2)$ by $c_{r-1}+2$. Thus the move equals the list
entry for its position $i$.

*Well-definedness.* Fix $i$ with $c_i=2$ and let $p$ be as in the list.
All parts of $p$ are parts of $c$ except the merged block, which is
$2+c_{i+1}\ge4$ (for $i\le r-1$; note $c_{i+1}\ge2$ as $c$ is support)
resp. $c_{r-1}+2\ge4$ (for $i=r$); hence $p$ is a support composition of
$d+2$. Its last part is $c_r\ge2$ (case $i\le r-2$), $2+c_r\ge4$ (case
$i=r-1$), resp. $c_{r-1}+2\ge4$ (case $i=r$) — in each case $\ge2$, so
$p$ corresponds to a genuine subset of $[d]$. The indicated move of $p$ is
selected: in the first case the merged block sits at index $i\le r-2 =
s-1$ where $s=r-1$ is the number of blocks of $p$, i.e. at a nonfinal
index, and has size $\ge4$, so its (N)-move (offset $2$) is selected and
by construction its child is $c$; in the second and third cases the merged
block is the final block of $p$, of size $\ge4$, whose (FL)- resp.
(FR)-move is selected, again with child $c$ by construction.

*Injectivity.* The position of the created $2$ of the listed move for $i$
is $i$ itself; distinct $i$ give moves with distinct created-$2$
positions, hence distinct moves.

*Aliasing.* Suppose two moves in the list realize the same cover edge. A
cover edge determines its parent subset and its added element $j$, and by
the dictionary of Section 2 the pair $(i_{\mathrm{split}},p)$ of split
block and offset is determined by $j$; so the two moves have the same
parent composition and split the same block at the same offset. Two
*distinct* selected moves of one parent with the same block and offset
exist, by Definition 4, only for (FL) and (FR) on a final block of size
$4$ (where $p=2=n_r-2$). In the list, this configuration occurs iff the
entries for $i=r-1$ and $i=r$ are both present and have equal parents,
i.e. $(c_1,\dots,c_{r-2},2+c_r)=(c_1,\dots,c_{r-2},c_{r-1}+2)$; given
$c_{r-1}=c_r=2$ (both positions carry $2$-blocks) this holds, the merged
final block is $4$, and the two moves realize the one coincident edge with
total flow $2G(c)$. In every other situation distinct list entries give
distinct edges. (In particular, entries at distinct positions
$i<i'\le r-2$ even have distinct parents: the parent for $i$ has the
merged block $2+c_{i+1}\ge4$ at position $i$, while the parent for $i'$
retains $c_i=2$ there.)

*Flow.* By Definition 4 every selected move has move-flow
$G(\text{child})$; here the child is $c$, so each move contributes $G(c)$.

Summing: inflow$(c)$ is the sum of $f$ over cover edges entering $c$,
which by Definition 4 equals the sum of move-flows over all selected moves
with child $c$ (the coincident edge, when present, carries the sum of its
two move-flows). By the bijection this sum is
$\#\{i:c_i=2\}\cdot G(c)$. $\square$

**Remark (boundary instances of Lemma 7).** If $r=1$ then $c=(d+2)$ with
$d+2\ge3$, so $c$ has no $2$-block and no in-edges — consistent, since a
selected move always produces a child with $\ge2$ blocks. If $r=2$ the
case $i\le r-2$ is vacuous; $c=(2,c_2)$ has the single (FL)-parent
$(2+c_2)$, $c=(c_1,2)$ the single (FR)-parent $(c_1+2)$, and
$c=(2,2)$ (i.e. $d=2$) both — coinciding as the single edge
$(4)\to(2,2)$ with flow $2G((2,2))$, matching its two $2$-blocks.
Consecutive $2$'s at positions $i,i+1\le r-2$ cause no coincidence, as
shown in the aliasing step.

## 7. Proof of Theorem 1

Let $c=(c_1,\dots,c_r)$ be a support composition of $d+2$. By Corollary 6
and Lemma 7,

$$\operatorname{div}f(c)
=G(c)\sum_{i:\;c_i\ge4}\rho(c_i)\;-\;\#\{i:c_i=2\}\cdot G(c).$$

Since $\rho(2)=-1$ and $\rho(3)=0$,

$$-\#\{i:c_i=2\}=\sum_{i:\;c_i=2}\rho(c_i)
\quad\text{and}\quad
0=\sum_{i:\;c_i=3}\rho(c_i),$$

whence
$\operatorname{div}f(c)=G(c)\sum_{i=1}^r\rho(c_i)=w(c)$ by (W).

Now let $K\subseteq[d]$ be a non-support subset (some part of $c(K)$
equals $1$). No selected move has $K$ as parent (selected moves are
defined only for support compositions) and none has $K$ as child (children
of selected moves are support compositions, by Definition 4). Hence
$f$ vanishes on every edge incident to $K$ and
$\operatorname{div}f(K)=0=w_K$ by Lemma 1.

Thus (D) holds at every $K\subseteq[d]$, and $f\ge0$ by construction, so
Lemma 2 yields Theorem 1 with the explicit coefficients

$$\lambda_{(J,\,J\cup\{j\})}=f\big(J\to J\cup\{j\}\big)=
\begin{cases}
G\big(c(J\cup\{j\})\big), & \text{single selected move on the edge},\\
2\,G\big(c(J\cup\{j\})\big), & \text{final block }4\to(2,2),\\
0, & \text{edge on no selected move},
\end{cases}$$

and $\lambda_{(J,J')}=0$ for non-cover pairs. $\blacksquare$

**Theorem 1$'$ (the certificate, summarized).** With
$G$ as in Definition 3, the nonnegative flow assigning
$G(\text{child})$ to the split $n_i\to(2,n_i-2)$ of every nonfinal block
$n_i\ge4$ and to both splits $n_r\to(2,n_r-2)$, $n_r\to(n_r-2,2)$ of the
final block $n_r\ge4$ of every support composition (values adding on the
coincident edge when $n_r=4$) satisfies
$\operatorname{div}f=w$ and hence realizes (1).

**Boundary case $d=1$.** The only support composition is $(3)$; it admits
no selected move (no block $\ge4$), so $f\equiv0$, and indeed
$w((3))=G((3))\rho(3)=0$; all other $J\subseteq[1]$ are non-support. Thus
(1) holds with all $\lambda=0$, as it must: for $d=1$ every $a_J=0$.

## 8. Computational cross-checks (not used in the proof)

The proof above is uniform in $d$ and requires no computation. As
corroboration only: the divergence identity (D), the positivity, and the
support of $f$ were verified in exact integer arithmetic at every support
node for every $d\le25$ (121\,393 nodes and 364\,057 selected edges at
$d=25$), and over all $2^d$ subsets (including non-support nodes) for
$d\le10$; Lemma 5 was verified for all $m\le200$ in varied contexts; the
constructive classification of Lemma 7 was verified by exhaustive forward
enumeration (exact multiset equality of (parent, block, offset) triples
per child) for $d\le14$. A related empirical observation — that the
"staircase" sets $T_k=\{2,4,\dots,2k\}\cup\{2k+1,\dots,d\}$ are the
*only* subsets $T$ with $\sum_{J\subseteq T}w_J=0$ — is **conjectural**
(verified for $d\le14$) and is used nowhere in this paper.

---

---

## External-review checklist (not part of the paper text)

A referee verifying this draft should independently check, at minimum:

1. **Statement fidelity.** The definitions of $U_J$, $a_J$ and the
   statements of Lemma 3.29 / Corollary 3.28 / Conjecture 3.30 against
   arXiv:2603.21680v3 §3.4, including the direction of (M$_{J,J'}$)
   (smaller set on the smaller side) and the reading of "nonnegative
   linear combination" as the linear-form identity (1).
2. **Composition dictionary.** The bijection $J\leftrightarrow c(J)$; that
   $n_{m+1}\ge2$; the cover-edge dictionary including the final-block
   offset bound $p\le n_r-2$ and the legality of the (FR) element $j=d$.
3. **Lemma 2.** The coefficient comparison at each $N_K$, and that the
   divergence sign convention (out minus in) matches the bracket order in
   (1); confirm no telescoping/chain argument is needed for this
   direction.
4. **Identity (W).** $U_ca_c=G(c)\sum\rho(n_i)$ directly from the
   definitions.
5. **Lemma 5.** All three factorial computations, in particular the
   last-part prefactor $n_r$ entering the (FL) and (FR) ratios, and the
   final identity $\frac{(m-2)(m-3)}{2}+(m-3)=\rho(m)$.
6. **Corollary 6.** That edge-sums equal move-sums (coincident final-$4$
   edge), and that blocks of size $2,3$ contribute no outflow.
7. **Lemma 7.** Each of the five steps (completeness, well-definedness,
   injectivity, aliasing, flow), and separately: the position ranges
   $\le r-2$ / $=r-1$ / $=r$ and their disjointness; the terminal $(2,2)$
   multiplicity; that consecutive interior $2$'s do not alias; that the
   parents constructed are support compositions with last part $\ge2$.
8. **Theorem.** The bookkeeping $\rho(2)=-1$, $\rho(3)=0$; the vanishing
   of $f$ and $w$ at non-support nodes; the boundary case $d=1$.
9. **Independence from computation.** No step of §§1–7 appeals to §8.
