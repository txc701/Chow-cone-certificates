# Shared degree-five gate and uniform `k=4` proof checkpoint

This checkpoint starts after the bounded `d=11` quotient commit
`0457403cda9800beea75b983b844e26716f13466`.  It does not change `main`, Lean,
the frozen `k=2` proof, or any earlier `k=4` artifact.

## Exact shared-coefficient decision

The cumulative system uses one ordered coefficient vector for every dimension
`d=2,...,11`.  The 524 columns are defined before evaluating any dimension:

```text
276 unchanged desymmetrized weighted-degree-<=4 columns
+248 systematic exact weighted-degree-5 columns
=524 columns.
```

Every dimension evaluates this same symbolic list.  No zero or coincident
small-dimensional evaluation column is removed.  The raw exact system has

```text
374 equations, 524 columns, 856 allowed edges,
rank(A)=360, rank([A|b])=360, nullity=164.
```

Thus the equality system is consistent.  This is not a nonnegativity result
and not an all-d theorem.

The complete exact affine space is stored in a deterministic direct-sum form.
Let `E` be the 856-by-524 normalized edge-evaluation map.  Then

```text
rank(E)=407,
dim ker(E)=117,
dim ker(A)=164,
dim(ker(A)/ker(E))=47.
```

The saved particular solution is supported on the deterministic min-column
section of `E`; 117 saved vectors span the edge-invisible coefficient gauge,
and 47 saved vectors span the evaluated divergence-free flow directions.  The
particular solution has 373 negative and 483 positive tested edge values.  It
is only a reproducible coordinate section, not a structural or nonnegative
formula.  No conclusion is made about nonnegativity of the other affine-family
members.

Expanding that section gives six exact channel polynomials.  Their monomial
counts are

```text
s2: left 113, right 112, balanced 32;
s3: left 53,  right 53,  balanced 31.
```

Exact round-trip evaluation reproduces all 856 edge values.  The large
coefficients and density make this a poor proof mechanism even though it is a
valid matrix solution.

## Proof-directed outcome

Two algebraically distinct routes--primitive divergence identities and a
product-rule lift of the proven `k=2` flow--give the same all-d signed identity

```text
(30V(child)+30N-12)F2 + 72F3 - 48F4.
```

Its divergence is exactly `G S4` for arbitrary support block variables and
every `d>=3`; this is a symbolic identity, not interpolation.  A recursive
equal-endpoint path-square construction eliminates every negative `F4` move.
Final-right moves create a right-peel debt whose block parameter decreases by
two at each step and terminates on an existing `F2` or `F3` edge.

The nonnegativity proof controls all colliding cascades.  With
`a(n)=(n-1)/n!`, the total normalized collision factor is bounded by

```text
sum_j 2^j a(y+2j)/a(y) <= 25/16,
```

and is `<5/4` at the odd `F3` terminal.  The three worst-case reserve margins
for block size `M>=6` are

```text
18M^2-66M+69,
18M^2-42M-36,
6M^2+18M-12,
```

all strictly positive.  The cases `M=4,5`, balanced multiplicities, `d=1`,
and `d=2` are handled explicitly.  The resulting flow is nonnegative and uses
only peel-width-2 and peel-width-3 cover edges.

The full proof, including the finite-poset linear-combination deduction, is
`PROOF_K4_FOURTH_MOMENT.md`.  Exact code independently corroborates every
state and edge for `d=1,...,11`; those checks are not premises of the proof.

## Relation to the degree-five grammar

The proof flow is not the saved polynomial particular solution.  In fact its
tested edge vector is outside the full 524-column feature image:

```text
rank(E)=407, rank([E|h_proof])=408.
```

A primitive two-row witness occurs at `d=4`.  The proof flow has normalized
values `360` and `144` on

```text
(2,4)->(2,2,2),       (4,2)->(2,2,2),
```

while every current balanced feature is mirror-invariant and gives the same
value on this reversed pair.  The witness pairing is `216`.

This rules out only representation of this particular recursive certificate
by the current local grammar.  It does not show that the consistent
164-dimensional affine family lacks a nonnegative member.  Conversely, the
uniform proof no longer needs that bounded feasibility question.

Method D (cut duality) was also examined independently.  It gives the exact
lower-ideal criterion and a marked-composition generating function, but no
closed positivity proof for arbitrary peel-three ideals.  That route is not
used by the successful constructive argument.
