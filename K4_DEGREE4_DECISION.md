# k=4 weighted-degree-four decision checkpoint

Date: 2026-08-24

Branch base: `f3efcfd4fa718884ed9934590af83f46c0772a00`

Scope: exactly one finite decision experiment. No Lean formalization, no
change to the frozen k=2 work, no feature or degree enlargement, and no all-d
claim.

## 1. The exact ansatz class

An allowed peel-width-three edge is written

```text
e = (A,m,B; p,q),     p+q=m,     s=min(p,q) in {2,3},
```

where the parent composition is `A ++ (m) ++ B` and the child replaces `m`
by `(p,q)`. Put `v(n)=n(n-2)` and define

```text
z  = m - 2s = |p-q|,
L  = sum of blocks in A,          R  = sum of blocks in B,
VL = sum v(n) over A,             VR = sum v(n) over B,
QL = sum v(n)^2 over A,           QR = sum v(n)^2 over B.
```

The weighted degrees are

```text
deg(z)=deg(L)=deg(R)=1,
deg(VL)=deg(VR)=2,
deg(QL)=deg(QR)=4.
```

The polynomial is imposed on the normalized flow

```text
h(e) = f(e) / G(child).
```

Since `G(child)>0`, nonnegativity of `h` is equivalent to nonnegativity of the
actual edge flow `f`.

### Mirror involution

Full composition reversal is the genuine graph involution

```text
rho(A,m,B; p,q) = (reverse(B),m,reverse(A); q,p).
```

It acts on the feature vector by

```text
sigma(z,L,R,VL,VR,QL,QR) = (z,R,L,VR,VL,QR,QL),
```

exchanges left and right peels, and fixes balanced peels. This is a symmetry
of the allowed split graph and of `S4`, but not of the normalized divergence
operator: the distinguished last block in `G` gives

```text
G(reverse(c)) / G(c) = first_block(c) / last_block(c).
```

Thus `h(rho(e))=h(e)` is an explicit ansatz restriction, not a property
inferred from the nonunique max-flow certificates or from the divergence
equations. In particular, final edges cannot be given an independent
coefficient family in this full-reversal-invariant class: reversal maps them
to first-block edges.

### Complete symmetry basis

All monomials of weighted degree at most four were enumerated before solving.
The involution decomposes their span into invariant and anti-invariant pieces:

| exact weighted degree | all | invariant | anti-invariant |
|---:|---:|---:|---:|
| 0 | 1 | 1 | 0 |
| 1 | 3 | 2 | 1 |
| 2 | 8 | 5 | 3 |
| 3 | 16 | 9 | 7 |
| 4 | 32 | 18 | 14 |
| total | 60 | 35 | 25 |

For each peel width `s`, an unbalanced edge has

```text
h(e) = P_s^+(x_e) + epsilon(e) P_s^-(x_e),
```

where `P_s^+` is invariant, `P_s^-` is anti-invariant, and `epsilon` is `+1`
for a left peel and `-1` for a right peel. Balanced edges use an invariant
polynomial. Because every balanced edge has `z=0`, removing invariant basis
elements that vanish identically there leaves 18 effective balanced terms.
The complete class therefore has

```text
2 peel widths * (35 invariant + 25 anti-invariant + 18 balanced) = 156
```

dimension-independent rational coefficients. The full exponent lists,
orbit-sum/orbit-difference basis, mirror action, parameter order, and variable
definitions are persisted in `results/k4_degree4_decision/basis.json`.

## 2. Direct exact training problem

No saved certificate coordinate is read. Substituting the ansatz directly
into

```text
sum_out [G(child)/G(parent)] h(e) - sum_in h(e) = S4(c)
```

for every composition in `d=2,...,12` produces an exact sparse rational
system with:

| equations | allowed edges evaluated | coefficients | rank(A) | rank([A|b]) |
|---:|---:|---:|---:|---:|
| 607 | 1529 | 156 | 155 | 156 |

The complete serialized matrix is
`results/k4_degree4_decision/training_system.json`. All entries use reduced
integer numerator/denominator strings. No floating-point fitting,
interpolation, or regression is involved.

The equality system is inconsistent. Consequently the equality-plus-
nonnegativity problem is infeasible a fortiori; no separate inequality solver
or numerical evidence is needed.

## 3. Exact decision witness

Training on `d=2,3` is consistent. A saved exact coefficient vector with all
free coefficients set to zero has only

```text
s2:oriented:invariant:00 = 300,
s2:balanced:invariant:00 = 240
```

nonzero, and verifies every one of those five preceding equations.

Adding `d=4` is already inconsistent: `rank(A)=5` and `rank([A|b])=6`. Let
`E_c` denote the exact divergence equation at composition `c`. The integer
combination

```text
- E_(2,2,2) + 2 E_(2,4) - 2 E_(4,2)
```

has zero coefficient in every one of the 156 ansatz columns. Its right-hand
side is

```text
-(-504) + 2(-24) - 2(-24) = 504,
```

so it asserts `0=504`. This three-row witness is saved with canonical row
labels and primitive integer multipliers in
`results/k4_degree4_decision/inconsistency_witness.json`. The standalone
verifier reads the serialized matrix independently of the generator and checks
all 156 zero column sums and the nonzero right-hand side exactly. Together
with the verified `d=2,3` solution, it proves that `d=4` is the smallest
inconsistent maximum training dimension.

Here, the verifier's `verified` flag is deliberately an internal-certificate
claim: it checks the saved basis metadata, matrix encoding, prefix solution,
witness, and decision exactly. It does not independently reconstruct the full
matrix from the composition model. That separate construction check is covered
by the exact generator tests, including an independent small-d divergence-sign
test, and by byte-identical deterministic regeneration.

## 4. Decision and stopping rule

There is no normalized flow in the specified complete, full-reversal-
invariant, weighted-degree-at-most-four polynomial class that satisfies even
the exact divergence equalities on `d=2,...,12`. Hence there is certainly no
such flow satisfying the equalities and edgewise nonnegativity.

Because no training coefficient vector exists, `d=13,...,16` are not evaluated
as holdouts. A failed training class cannot be repaired or meaningfully tested
on holdouts without refitting, which is forbidden here. No degree increase,
feature addition, alternate symmetry convention, or second search was
launched.

The result does **not** rule out all weighted-degree-four rules without mirror
invariance, and it does not challenge the finite peel-width-three feasibility
certificates. It specifically rules out the 156-dimensional class defined
above. The small witness indicates that ordinary reversal invariance is
incompatible with the distinguished-final-block factor in `G` already at
`d=4`.

The next conceptual direction is therefore not a higher-degree search. It is
to derive, before any computation, a boundary-aware or `G`-covariant
transformation law that replaces the invalid ordinary condition
`h(rho(e))=h(e)`. Such a law would need symbolic justification from the
composition model; it was not formulated or tested in this checkpoint.

## 5. Reproduction and evidence

Run exactly:

```bash
PYTHONPATH=src python3 src/run_k4_degree4_decision.py \
  --output-dir results/k4_degree4_decision
```

The output manifest hashes the basis, full training matrix, preceding-prefix
solution, inconsistency witness, decision, verification summary, and all source
modules required to reproduce them. It contains no timestamps or runtime
measurements.

The focused k=4 checkpoint suite has 114 passing tests. The completed
degree-four decision file accounts for eight of them. Running the remaining
repository suite with that already-completed file excluded gives 277 passes
and one pre-existing failure, so the combined current-tree result is 285
passes and that same one failure:
`tests/test_weights.py::test_no_floating_point_in_sources` rejects the exact
`Fraction` division already present in the untouched `src/k4_weights.py` at the
base checkpoint. None of the new source files introduces a forbidden division,
floating literal, or `float` call.

The Lean/Conjecture 3.30 line remains frozen at main commit `65e1056`. No Lean
file, pre-existing result artifact, existing mathematical definition, or k=2
file is changed by this checkpoint.
