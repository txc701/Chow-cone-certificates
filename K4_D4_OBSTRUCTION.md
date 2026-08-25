# Exact `d=4` obstruction at checkpoint `7c37334`

This note analyzes only the saved inconsistency witness for the normalized
flow ansatz. It does not enlarge or solve the ansatz, evaluate a new dimension,
or change any frozen k=2 or Lean file.

## 1. The three equations

Write `h(e)=f(e)/G(child)` as in the checkpoint. The five width-at-most-three
edges at `d=4` include the two reversal pairs

```text
x  : (2,4) -> (2,2,2),       x' : (4,2) -> (2,2,2),
y  : (6)   -> (2,4),         y' : (6)   -> (4,2).
```

The `G(child)/G(parent)` ratios on `x,x'` are respectively `1,2`. Ordinary
reversal invariance of the tested normalized ansatz gives

```text
h(x)=h(x')=:A,     h(y)=h(y')=:B.
```

The exact target constants follow from `B4_720(4)=504`. For `(2,2,2)` every
block statistic `m(m-2)` vanishes, giving `S4=-504`. For `(2,4)` and `(4,2)`,
the block-4 contribution is `3*4*2*20=480` and the cross term is zero, giving
`S4=-24`.
Therefore the three complete edgewise equations are

```text
E_(2,2,2):  -h(x)-h(x')       = -504,
E_(2,4):     h(x)-h(y)         =  -24,
E_(4,2):    2h(x')-h(y')       =  -24.
```

For a literal expansion in the 156 saved columns, let

```text
a0,...,a4 = s2:balanced:invariant:{00,01,03,07,14},
b0,...,b4 = s2:oriented:invariant:{00,02,07,16,34}.
```

These are respectively `1,L+R,L^2+R^2,L^3+R^3,L^4+R^4` on balanced edges
and `1,z,z^2,z^3,z^4` on oriented edges. Hence

```text
A = a0 + 2a1 + 4a2 + 8a3 + 16a4,
B = b0 + 2b1 + 4b2 + 8b3 + 16b4,
```

and the three rows are exactly

```text
E_(2,2,2): -2a0-4a1-8a2-16a3-32a4                         = -504,
E_(2,4):    a0+2a1+4a2+ 8a3+16a4-b0-2b1-4b2-8b3-16b4     =  -24,
E_(4,2):   2a0+4a1+8a2+16a3+32a4-b0-2b1-4b2-8b3-16b4     =  -24.
```

Every unlisted column has coefficient zero in all three rows. More precisely,
all 78 width-three columns vanish; all 25 width-two oriented anti-invariant
columns vanish at the mirror-fixed feature vector `(z,L,R,VL,VR,QL,QR) =
(2,0,0,0,0,0,0)`; and 30 remaining oriented-invariant plus 13 remaining
balanced-invariant width-two columns contain a zero feature. Thus 146 columns
vanish termwise and only the ten displayed columns need cancellation.

## 2. Obstruction lemma

**Lemma (reversal obstruction).** Let `h` be any normalized edge assignment at
`d=4` satisfying `h(e)=h(rho(e))` under composition reversal. Then the linear
functional

```text
W = -E_(2,2,2) + 2E_(2,4) - 2E_(4,2)
```

annihilates the divergence of `h`.

Indeed, before imposing reversal invariance its left side is

```text
3(h(x)-h(x')) - 2(h(y)-h(y')).
```

Both differences vanish. Equivalently, the displayed parameter expansion gives
`2A + 2(A-B) - 2(2A-B)=0` column by column. But its target is

```text
-(-504) + 2(-24) - 2(-24) = 504.
```

Consequently no reversal-invariant normalized flow can satisfy these three
equations.

This proof uses only ordinary scalar mirror invariance. It does **not** use the
weighted-degree-four cutoff, polynomiality, the seven-variable feature list,
or locality: an arbitrary-degree, arbitrary-feature, even nonlocal rule still
has the same contradiction if it forces `h(e)=h(rho(e))`. Conversely, the
existing local variables already contain a degree-one direction that escapes
the witness. The essential restriction is therefore mirror invariance, not the
degree bound, chosen raw features, or locality.

## 3. Minimal extension proposal, without a solve

At least one column outside the witness kernel is necessary. One column is also
sufficient to defeat this witness, although the choice is not unique. The
principled proposal is the boundary feature

```text
phi_G(e) = first block of child(e)
```

on oriented peel-width-two edges, and zero on the other channels. This feature
is local, dimension-stable, nonnegative, and of natural weight one. More
importantly, it obeys the covariance suggested by the distinguished-final-block
factor in `G`. If `c=child(e)`, then

```text
G(c) phi_G(e) = G(reverse(c)) phi_G(rho(e)).
```

Indeed `G(reverse(c))/G(c)=c_first/c_last`, while `phi_G` changes from
`c_first` to `c_last`. Thus this column is reversal-invariant for the
unnormalized flow `f=G(child)h`, rather than incorrectly invariant for `h`.

For the two root edges the exact data are

```text
child       G(child)    phi_G
(2,4)          30          2
(4,2)          15          4
```

and both products are `60`. On the three witness rows the new divergence column
is

```text
E_(2,2,2): 0,     E_(2,4): -2,     E_(4,2): -4,
```

so `W(phi_G)=4`, not zero. A coefficient `126` would satisfy this one necessary
witness equation because `126*4=504`; this is not a claim that the remaining
divergence equations or nonnegativity constraints are feasible.

This one-dimensional `156 -> 157` proposal is minimal in parameter dimension.
It needs neither a degree increase nor a large raw feature expansion. `phi_G`
is nominated because it implements the natural boundary covariance instead of
an arbitrary symmetry break. No extended equality or nonnegativity solve is
run at this gate.

## 4. Exact checks and unrelated known failure

`tests/test_k4_d4_obstruction.py` verifies the complete named row expansions,
all 156 zero column sums, target value `504`, both reversal pairs, and the exact
`G`-covariant new-column value `4`.

The single pre-existing repository failure is
`tests/test_weights.py::test_no_floating_point_in_sources`. It rejects the `/`
token in the exact `Fraction` computation at `src/k4_weights.py:63`. That source
line predates checkpoint `7c37334`; this obstruction checkpoint does not modify
it or introduce floating-point arithmetic, so the failure is unrelated.
