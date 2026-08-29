# A uniform peel-three certificate for the fourth-moment inequality

**Status.** This document gives a symbolic construction for every dimension.
The finite computations in the repository only corroborate the formulas; they
are not used in the proof.  The argument is new and should receive external
human review before publication.  It does not modify or depend on the frozen
Lean proof of the `k=2` result.

## 1. Statement

Fix `d >= 1` and put `N=d+2`.  A support composition is

```text
c=(n_1,...,n_r),    n_i >= 2,    sum_i n_i=N.
```

Write

```text
v(n)=n(n-2),       V(c)=sum_i v(n_i),       Q(c)=sum_i v(n_i)^2,
G(c)=U_c product_i(n_i-1)
    =(N-1)! n_r product_i ((n_i-1)/n_i!).
```

The scaled fourth-moment target is `w^(4)(c)=G(c)S_4(c)`, where

```text
S_4(c)=15V(c)^2-6Q(c)-12V(c)-B_d.
```

Here `B_d=720 mu_4(X_d)` for the Boolean matroid.  Thus

```text
B_d=15N^2-6N  for d>=3,
B_2=240,
B_1=45,
```

and the sole support state at `d=1` has target zero.

**Theorem.** For every `d>=1` there is a nonnegative raw flow `f_d` on the
support-composition DAG, supported on cover splits

```text
n -> (p,n-p),       min(p,n-p) <= 3,
```

such that `div(f_d)(c)=w^(4)(c)` at every support composition.  Extending the
flow by zero off the support proves that the fourth-moment flag inequality is
a nonnegative linear combination of the Cheng--Lin monotonicity inequalities.
Throughout, `div` means outgoing flow minus incoming flow, and every displayed
split is oriented from the coarser parent to the finer child.

The rest of the document defines `f_d` and proves the theorem.

## 2. Three primitive flows

Set

```text
a(n)=(n-1)/n!,       so G(c)=(N-1)! n_r product_i a(n_i).
```

For `s` in `{2,3,4}`, define the move-multiset `F_s` as follows.  From every
nonfinal block `m>=s+2`, select the move

```text
m -> (s,m-s).
```

From a final block `m>=s+2`, select both

```text
m -> (s,m-s),       m -> (m-s,s).
```

Each selected move carries raw flow `G(child)`.  If `m=2s`, the two final
labels denote the same cover edge and their flows are added.  Retaining these
labels as a multiset avoids every balanced-edge ambiguity below.

Define

```text
tau_2(n)=n(n-3)/2,
tau_3(n)=n(n-2)(n-4)/3,
tau_4(n)=n(n-2)(n-3)(n-5)/8,
T_s(c)=sum_i tau_s(n_i).
```

### Lemma 1 (primitive divergences)

For `d>=3`,

```text
div(F_s)(c)/G(c)=T_s(c),       s=2,3,4.
```

**Proof.** If a nonfinal block `m` is split at `s`, direct cancellation in
the formula for `G` gives

```text
G(child)/G(parent)
 = binom(m,s)(s-1)(m-s-1)/(m-1).
```

For a final block, the left and right ratios acquire the factors `(m-s)/m`
and `s/m`; their sum is the same nonfinal ratio.  At `s=2,3,4`, the
nonfinal ratio, and the sum of the two final ratios, is exactly `tau_s(m)`
as displayed above.

Every occurrence of a block `s` in a child has one incoming selected move:
merge it with its right neighbour if it is nonfinal, and merge it with its
left neighbour if it is final.  The last two blocks both equal to `s` exactly
produce the doubled balanced move.  Consequently the normalized inflow is
one for each `s`-block.  The polynomial `tau_s` has value `-1` at `s` and
vanishes at every other support block smaller than `s+2`, so outgoing minus
incoming is `sum_i tau_s(n_i)`.  For `d>=3`, a `3`- or `4`-block cannot be the
exceptional sole support block, completing the boundary check.  ∎

Let `F_{2,V}` be the same move-multiset as `F_2`, but give a move the raw
flow `G(child)V(child)`.

### Lemma 2 (discrete product rule)

For `d>=3`,

```text
div(F_{2,V})/G = V(V-N)/2 - 6T_3 - 2V.
```

**Proof.** Lemma 1 gives `T_2=(V-N)/2`.  A selected split
`m -> (2,m-2)` changes `V` by `-4(m-2)`.  Moving the child potential through
the divergence therefore gives

```text
div(F_{2,V})/G
 = V T_2 + sum_i [-4(n_i-2)tau_2(n_i)].
```

The one-variable polynomial identity

```text
-4(n-2)tau_2(n) = -6tau_3(n)-2v(n)
```

gives the result.  ∎

The second polynomial identity needed below is

```text
v(n)^2-9v(n)=8tau_4(n)+18tau_3(n),
```

and hence

```text
Q-9V=8T_4+18T_3.                         (1)
```

### Proposition 3 (signed fourth-moment identity)

For `d>=3`, the signed raw flow

```text
f_0=(30V(child)+30N-12)F_2 + 72F_3 - 48F_4                 (2)
```

has divergence `G S_4`.

**Proof.** Multiply Lemma 2 by `30`, add `(30N-12)` times Lemma 1 for
`F_2`, and then add `72T_3-48T_4`.  Using `T_2=(V-N)/2` and (1), the result
simplifies exactly to

```text
15V^2-6Q-12V-15N^2+6N=S_4.
```

No dimension has been evaluated in this calculation.  ∎

The `F_2` coefficient in (2) is positive because `V(child)>=0` and `N>=5`.
The `F_3` coefficient is positive.  Only `-48F_4` prevents (2) from already
being a certificate.

## 3. Eliminating every negative `F_4` move

Concatenation notation such as `P.(4,t).S` means an arbitrary prefix `P`,
the displayed consecutive blocks, and an arbitrary suffix `S`.  Every
correction below is a difference of two directed paths with the same endpoints,
so it has zero divergence.

### 3.1 Nonfinal and final-left moves

Let

```text
A=P.(t+4).S,       B=P.(4,t).S,
C=P.(2,t+2).S,     D=P.(2,2,t).S,       t>=2,
```

where `A->B` is either a nonfinal `F_4` move or the final-left `F_4` move.
There are two paths from `A` to `D`:

```text
A -> B -> D,       A -> C -> D.
```

All three edges other than `A->B` peel a `2`.  Put `R=48G(B)` and add

```text
R[(A->B)+(B->D)-(A->C)-(C->D)].                         (3)
```

This cancels the `-48G(B)` on `A->B`, adds flow on `B->D`, and consumes
flow only from the two selected `F_2` edges `A->C` and `C->D`.  Relative to
the `G(child)` normalization, the consumptions are

```text
A->C: 12(t+2)(t-1)  if the original block is nonfinal,
      12t(t-1)      if it is final;
C->D: 24.
```

These formulas follow immediately by dividing `48G(B)` by the corresponding
child `G` values.

### 3.2 Final-right moves and the cascade

For a final-right `F_4` move put

```text
A=P.(t+4),       B=P.(t,4),
C=P.(t+2,2),     D=P.(t,2,2),       t>=2.
```

Adding the analogue of (3) cancels `A->B`, adds flow on the final
`4->(2,2)` edge, and consumes

```text
24(t+2)(t-1)
```

from the selected final-right `F_2` edge `A->C`.  It leaves a negative raw
amount `R=48G(B)` on the nonfinal right peel

```text
C -> D,       (t+2)->(t,2).                              (4)
```

The debt (4) is shifted down by path squares.  At a general stage write

```text
X_j=P.2^j.(y+2,2),       Y_j=P.2^j.(y,2,2),
Z_j=P.2^(j+1).(y,2),     W_j=P.2^(j+1).(y-2,2,2),
```

where `2^j` means `j` consecutive blocks equal to `2`, `y=t-2j`, and
`y>=4`.  The two paths

```text
X_j -> Y_j -> W_j,       X_j -> Z_j -> W_j
```

give another incidence identity.  Adding `R` times their difference cancels
the current negative right peel, adds `R` on the selected left-`F_2` edge
`Y_j->W_j`, consumes `R` on the selected left-`F_2` edge `X_j->Z_j`, and
moves the negative amount to

```text
Z_j -> W_j,       y -> (y-2,2).
```

Thus `y` decreases by two.  The process terminates: at `y=2` the final debt
is a selected `F_2` edge `4->(2,2)`, and at `y=3` it is the selected `F_3`
edge `5->(3,2)`.  The newly created `2` is retained in the prefix at every
stage; this is part of the definition of the recursion.

Apply (3) to every nonfinal/final-left `F_4` move-label and apply this
final-right procedure to every final-right label.  Because the corrections
are linear, their order is immaterial.  In particular, the two labels on the
balanced final edge `8->(4,4)` are cancelled separately, through the distinct
common descendants `(2,2,4)` and `(4,2,2)`.

The resulting flow has the same divergence as `f_0`.  Every surviving or
newly introduced edge peels a `2` or a `3`; no peel-`4` contribution remains.

## 4. Nonnegativity

It remains to prove that the subtractions in the preceding section never
exhaust their positive reserves.  The argument must account for collisions
between cascades; checking one correction in isolation would not suffice.

### Lemma 4 (cascade collision bound)

Fix a selected nonfinal-left `F_2` edge that is consumed at a cascade stage,
and write its affected block as `y+2`, so `y>=2` (`y=M-2` if that block has
size `M`).  Here `y=2` is the terminal `F_2` debt and `y>=4` describes an
intermediate cascade stage.  All final-right cascades that can consume this
same edge are uniquely indexed by a suffix of the finite consecutive `2`-run
immediately before its affected block.  The normalized amount from the
`j`-th possible origin is

```text
48 r_j,       r_j=2^j a(y+2j)/a(y).
```

Moreover,

```text
r_(j+1)/r_j = 2/[(y+2j+2)(y+2j-1)].                     (5)
```

Consequently

```text
sum_j r_j <= 1+(1/2)/(1-1/9)=25/16.                    (6)
```

For a fixed terminal `F_3` edge, the same `G`-ratio calculation has `y=3`
and gives the sharper estimate

```text
sum_j r_j <= 1+(1/5)/(1-1/14)=79/65 < 5/4.             (7)
```

**Proof.** Given either fixed edge, an origin is recovered uniquely by
deleting `j` blocks from the indicated finite `2`-run and replacing the
residual parameter `y` by `y+2j`; thus only the finitely many suffix lengths
available in that run occur.  No other prefix, affected block, or cover cut
can produce the same oriented edge.  Cancelling the common prefix factors in
`G`, including the distinguished final-block factor, gives the displayed
`r_j` in both the intermediate-`F_2` and terminal-`F_3` cases.  Formula (5)
follows from

```text
a(n+2)/a(n)=1/[(n+2)(n-1)].
```

For `y>=2`, the first ratio in (5) is at most `1/2` and every later ratio is
at most `1/9`, proving (6).  At `y=3` they are at most `1/5` and then `1/14`,
proving (7).  ∎

Thus all cascades together consume at most `75` normalized units from any
selected `F_2` edge and strictly less than `60` units from a terminal
selected `F_3` edge.

### Lemma 5 (capacity bounds)

Every edge remaining after the corrections has nonnegative flow.

**Proof.** A selected `F_2` move has initial normalized reserve

```text
H=30V(child)+30N-12.                                    (8)
```

There are only three ways to consume a fixed nonfinal-left edge: the unique
top square determined by its own parent and block; the unique bottom square,
possible when the affected block is immediately preceded by `2`; and the
final-right cascades classified in Lemma 4.  To see that this list is
exhaustive, retain a tag on every selected primitive move until all path
corrections have been made.  Reversing a top correction recovers its unique
parent and affected block.  Reversing a bottom correction first removes the
immediately preceding `2`, and then recovers the unique affected block.
Reversing a cascade correction removes a unique suffix of the preceding
`2`-run, exactly as in Lemma 4.  Different blocks cannot alias a Boolean
cover edge.

This occurrence-level bookkeeping also covers coincidences between the
`F_2`, `F_3`, and `F_4` families at final block sizes `5`, `6`, and `7`:
their tags remain distinct until their signed contributions are aggregated.
Likewise, the balanced final moves at block sizes `4`, `6`, and `8` have two
primitive labels.  The doubled `F_4` contribution is cancelled label by
label, while the doubled positive `F_2` or `F_3` reserve only strengthens the
bounds below.  Hence no further subtraction is hidden by an edge collision.
For the remaining orientations, reversal of the bookkeeping gives only the
initial final-right square, while a terminal debt lands on precisely the
`F_2` or `F_3` edge already classified above.  This exhausts every negative
term introduced by (3) and by the cascade.

For an affected nonfinal block of size `M`, use `N>=M+2` and
`V(child)>=(M-2)(M-4)`.  Its total possible consumption is at most

```text
12(M-2)(M-5)+24+75,
```

with the first term omitted for `M<6`.  For `M>=6`, subtracting this from
(8) leaves at least

```text
18M^2-66M+69 > 0.
```

For `M=4,5`, the reserves are at least `168,288`, respectively, while the
remaining possible consumption is at most `99`.

For a final-left block of size `M`, no cascade can consume the edge.  Its
total consumption is at most

```text
12(M-4)(M-5)+24,
```

and its reserve is at least

```text
30(M-2)(M-4)+30M-12.
```

For `M>=6` the margin is

```text
18M^2-42M-36 > 0;
```

the cases `M=4,5` are immediate.

For a final-right block of size `M`, the sole subtraction is its own initial
right square, of size `24(M-2)(M-5)` when `M>=6`.  The same lower bound for
the reserve leaves

```text
6M^2+18M-12 > 0.
```

For completeness, the three displayed margin polynomials have values
`321,360,312` at `M=6`, respectively, and first differences
`36M-48`, `36M-24`, and `12M+24`; hence their positivity holds for every
integer `M>=6`, not merely for a checked range.

At final `M=4`, the left and right `F_2` labels coincide, so the actual edge
has two copies of the reserve; this only strengthens the estimates.

Finally, a terminal `F_3` edge begins with normalized reserve `72` and loses
strictly less than `60` by (7).  Every correction not listed above is an
addition.  Hence all resulting raw edge flows are nonnegative.  ∎

Combining Proposition 3 with the zero-divergence corrections and Lemma 5
proves the theorem for every `d>=3`.

## 5. The two small dimensions

At `d=1`, the sole support composition is `(3)`, its fourth-moment target is
zero, and take `f_1=0`.

At `d=2`, the support DAG is the single edge

```text
(4) -> (2,2).
```

Here `G(4)=G(2,2)=3`, `S_4(4)=240`, and `S_4(2,2)=-240`, so define its raw
flow to be `3*240=720`.  Equivalently, the general signed construction contributes raw
flow `648` and the definition adds the missing raw `72` (normalized `24`).
Both the exceptional Boolean fourth moment and the unavailable singleton
`F_4` incoming move enter this boundary calculation, so the correction should
not be attributed to only one of them.

## 6. From the flow to the inequality

For a subset `J` with composition `c(J)`, let

```text
a_J^(4)=product_i(n_i-1) S_4(c(J)),
w_J^(4)=U_J a_J^(4)=G(c(J))S_4(c(J)),
x_J=N_J/U_J.
```

The target vanishes off the support because of `product_i(n_i-1)`, and the
constructed flow has no edge incident to an off-support node.  Extend `f_d`
by zero to the full Boolean cover DAG.  Since `div(f_d)=w^(4)`, finite
summation by parts gives the exact identity

```text
sum_J a_J^(4) N_J
 = sum_J w_J^(4) x_J
 = sum_(J -> J') f_d(J,J') [x_J-x_J'].
```

The fourth-moment flag decomposition itself is

```text
sum_J a_J^(4) N_J
 = 720 CH_M(1) [mu_4(X_M)-mu_4(X_d)],
```

where `CH_M(1)>0`.  Thus the flag inequality below is precisely the claimed
fourth-central-moment comparison, not merely a surrogate inequality.

Cheng--Lin's monotonicity lemma gives `x_J<=x_J'` whenever `J` is contained
in `J'`.  Every coefficient `f_d(J,J')` above is nonnegative, so the last
sum is at most zero.  This is exactly the required nonnegative linear
combination of the finite-poset inequalities and proves the intended scaled
fourth-moment inequality for every `d`.

## 7. Computational corroboration and the degree-five gate

`src/k4_uniform_certificate.py` is a direct transcription of the definition:
it forms (2), applies every path-square correction, aggregates coincident
cover edges, and handles `d=1,2` separately.  Two independent implementations
checked every state and edge for `d=1,...,11`: exact divergence, nonnegative
integer flow, zero total divergence, and peel width at most three.  These
checks test the transcription and boundary bookkeeping, not the theorem's
logical validity.

Separately, the systematic 524-column weighted-degree-at-most-five grammar is
exactly consistent with one shared coefficient vector on `d=2,...,11`:
`rank(A)=rank([A|b])=360`, with affine dimension `164`.  The coefficient
kernel splits into `117` directions invisible on every tested edge and `47`
evaluated divergence-free flow directions.  Its deterministic coordinate
section has many negative edges and is not a certificate; that fact says
nothing about the other points of the affine family.

Exact evaluation ranks `407/408` show that the uniform certificate's edge
values on `d=2,...,11` are not represented by the degree-five feature image.
The primitive two-row witness already occurs at `d=4`: the normalized flows
on the reversed balanced edges

```text
(2,4)->(2,2,2),       (4,2)->(2,2,2)
```

are `360` and `144`, whereas every balanced column in the current grammar is
mirror-invariant and evaluates equally on this pair.  The later cascade also
uses ordered terminal `2`-run information, but it is not needed for this
minimal representation obstruction.  This rules out only representation of
this particular recursive certificate in the current local grammar.  It is
neither a failure of the grammar's equality system nor a counterexample to the
fourth-moment statement.
