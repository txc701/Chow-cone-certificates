# Oriented degree-four lift: exact `d=4` equality gate

Base checkpoint: `59560a535c7c1ae3201a44215053ac24cc50b803`.
This gate does not modify any previous report or artifact, append `phi_G`, test
edge nonnegativity, or evaluate an equality system outside `d=4`.

## 1. Literal desymmetrized lift

The old 156-column class has, for each peel width `s=2,3`,

```text
35 oriented invariant + 25 oriented anti + 18 balanced invariant = 78
```

columns. The lift is performed on these exact column functions, not on a
larger raw-monomial class:

- each of the 60 oriented columns is restricted independently to left and
  right unbalanced edges;
- the right restriction of an anti column retains the minus sign already in
  the old column;
- each of the 18 balanced columns is already genuinely self-reversing and is
  retained once.

Thus the deduplicated count is

```text
per peel: 60 left + 60 right + 18 balanced = 138,
total:    2 * 138 = 276.
```

Adding the omitted balanced anti-invariant raw-monomial directions would give
a different 304-column feature enlargement. It is not part of this gate,
because the instruction is to start from the exact old column basis and keep
self-reversing columns single.

The gate generator deterministically produces
`basis_correspondence.json` with all 156 exact old-to-new rows. Every old
oriented coefficient maps with factor `1` to its left and right restrictions;
every balanced coefficient maps to its one fixed column. The 276 new columns
occur exactly once in that generated table.

Plain coefficient reversal swaps each left/right restriction pair and fixes
the 36 balanced columns. Its fixed-subspace dimension is therefore

```text
120 oriented pairs + 36 balanced singletons = 156.
```

The embedding duplicates each old oriented coefficient on its two restrictions
and leaves balanced coefficients unchanged. Conversely, a fixed lifted vector
has equal coefficients on each restriction pair and uniquely recovers the old
vector. Substitution reproduces every old edge-column row exactly. Hence the
old ansatz is exactly, not merely injectively, the fixed coefficient subspace.

## 2. Endpoint features are not appended

Neither `first(child)` nor `last(child)` is a global function of
`(z,L,R,VL,VR,QL,QR)` and the lifted side/peel channel. At `d=8`, the left
width-two edges

```text
((2,3,5), block 2, left 2),
((3,2,5), block 2, left 2)
```

have identical lifted features

```text
(z,L,R,VL,VR,QL,QR) = (1,5,0,3,0,9,0),
```

but their child-first blocks are `2` and `3`, while both child-last blocks are
`3`. A second same-feature pair

```text
((5,2,3), block 0, left 2),
((5,3,2), block 0, left 2)
```

holds the child-first block fixed at `2` while the child-last blocks are `3`
and `2`. These two collisions also rule out every nonzero linear combination
of the first/last orbit pair.

On the five `d=4` edges only, the restrictions happen to lie in the lifted
matrix span:

```text
first(child) = 2 * (s2 left constant) + 4 * (s2 right constant),
last(child)  = 4 * (s2 left constant) + 2 * (s2 right constant),
```

with both sides zero on the other channels. This finite-matrix coincidence is
not global feature membership. No named `phi_G` column is appended.

## 3. Exact `d=4` equality decision

Direct substitution gives a matrix with

```text
rows = 5, columns = 276, allowed edges = 5, nonzero entries = 37.
```

Exact rational elimination returns

```text
rank(A) = 4,
rank([A|b]) = 4,
nullity = 276 - 4 = 272.
```

The system is consistent. With all free coefficients set to zero, one exact
solution has only

```text
s2:left:invariant:00      = 276,
s2:right:invariant:00     = 528,
s2:balanced:invariant:00  = 252,
s3:balanced:invariant:00  = 144
```

nonzero. Every one of the five exact residuals is zero.

The old three-row witness no longer annihilates the class. It has ten nonzero
entries:

```text
s2 left  z^k: -2^(k+1),
s2 right z^k: +2^(k+1),       k=0,...,4,
```

and right-hand side `504`. Equivalently it requires

```text
sum_{k=0}^4 2^k (c_right,k - c_left,k) = 252.
```

For the displayed solution only the two constant terms contribute:
`528-276=252`. No coefficient named or identified with `phi_G` is privileged.

## 4. Evidence and stopping rule

The persisted `decision.json` records the solution, residuals, ranks,
nullity, and witness row. The gate source deterministically regenerates the
exact correspondence, full sparse `5 x 276` matrix, decision, and manifest
with hashes. Focused tests verify that generation as well as the embedding,
fixed subspace, endpoint-feature collisions, d=4-only scope, exact arithmetic,
and absence of floating-point or true-division syntax in the new source.

This gate stops after equality consistency. It does not perform edgewise
nonnegativity optimization, choose among the 272 free directions, or evaluate
any holdout dimension.
