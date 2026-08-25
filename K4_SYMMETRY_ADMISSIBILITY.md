# Reversal and admissibility audit after `edd9092`

This audit starts from the original nonnegative raw-flow problem. It does not
solve an enlarged ansatz or a new nonnegativity problem. The obstruction
checkpoint `edd9092`, its parent `7c37334`, main, Lean, and k=2 remain unchanged.

## 1. Exact reversal laws

Fix `d`, and let `C_d` be the support compositions of `d+2` with every part at
least two. For `c=(c_1,...,c_r)`, define

```text
rho(c) = (c_r,...,c_1).
```

Write an oriented split edge as

```text
e = (A,m,B; p,q): (A,m,B) -> (A,p,q,B),    p+q=m.
```

Then

```text
rho(e) = (reverse(B),m,reverse(A); q,p).
```

In zero-based edge-key notation this is

```text
rho(c,i,p) = (rho(c), len(c)-1-i, c_i-p).
```

It is an involution, sends `child(e)` to `rho(child(e))`, and preserves the
forward split orientation, support, and peel width.

For a raw edge flow `f`, set

```text
(R_raw f)(e) = f(rho(e)),
div(f)(c) = sum_{e out of c} f(e) - sum_{e into c} f(e).
```

The incidence matrix is carried to itself, so

```text
div(R_raw f)(c) = div(f)(rho(c)).
```

The original k=4 target is

```text
w(c) = G(c) S4(c),
alpha(c) = G(rho(c))/G(c) = c_1/c_r.
```

The statistic `S4` is symmetric in the blocks, but `G` distinguishes the last
block. Consequently

```text
S4(rho(c)) = S4(c),
w(rho(c)) = alpha(c) w(c).
```

Thus reversal permutes the raw divergence rows and their edge coefficients,
but rescales their right sides by the nonconstant factor `alpha(c)`.

Now normalize by the child:

```text
q(e) = f(e)/G(child(e)),
D_G q(c) = sum_{e:c->v} G(v)/G(c) q(e) - sum_{e:u->c} q(e).
```

The equation is `D_G q=S4`. The action on `q` induced by raw reflection is

```text
(Tq)(e)
  = G(rho(child(e)))/G(child(e)) q(rho(e))
  = alpha(child(e)) q(rho(e)).
```

It is an involution, and its exact row transformation is

```text
D_G(Tq)(c) = alpha(c) D_G(q)(rho(c)).
```

For residuals `E_c(q)=D_G q(c)-S4(c)`, equivalently

```text
E_c(Tq) = alpha(c) E_rho(c)(q) + (alpha(c)-1) S4(c).
```

The fixed-point covariance of this natural action is

```text
q(e) = alpha(child(e)) q(rho(e)),
```

or, equivalently, `G(child(e))q(e)=G(rho(child(e)))q(rho(e))`. This says the
raw flow is reversal-invariant. It is not the previously imposed scalar law
`q(rho(e))=q(e)`.

## 2. Reflection and averaging do not justify a WLOG restriction

Raw reflection preserves the directed support graph and nonnegativity. It does
not preserve the divergence target:

```text
div(f)=w  implies  div(R_raw f)(c)=w(rho(c))=alpha(c)w(c).
```

Even allowing rational flows, averaging gives

```text
div((f+R_raw f)/2)(c) = (w(c)+w(rho(c)))/2,
```

which is generally not `w(c)`. At `d=4`,

```text
G(2,4)=30,  G(4,2)=15,  S4(2,4)=S4(4,2)=-24,
w(2,4)=-720,             w(4,2)=-360.
```

The exact hand certificate in the tests reflects to the swapped target, and
its average has divergence `-540` at both `(2,4)` and `(4,2)`, rather than the
required values.

Therefore neither `q(rho(e))=q(e)` nor the natural raw-flow fixed-point
covariance is justified WLOG by a reflection-and-averaging argument. The latter
is the correct law for *how raw reflection acts* after normalization, but the
inhomogeneous target is not fixed by that action. This does not prove that no
feasible flow happens to lie in either subspace: the unrestricted system has
not been solved here. It proves only that reflection and averaging cannot force
a feasible flow into either fixed subspace.

## 3. Audit of the proposed column

On oriented (unbalanced) peel-width-two edges, define

```text
phi_G(e) = first block of child(e),
```

and set it to zero on balanced or width-three channels. Its complete `d=4`
table is

| edge | `G(child)` | `alpha(child)` | `phi_G` | plain partner `phi_G o rho` | `T phi_G` | raw `G(child)phi_G` |
|---|---:|---:|---:|---:|---:|---:|
| `(2,4)->(2,2,2)` | 30 | 1 | 0 | 0 | 0 | 0 |
| `(4,2)->(2,2,2)` | 30 | 1 | 0 | 0 | 0 | 0 |
| `(6)->(2,4)` | 30 | 1/2 | 2 | 4 | 2 | 60 |
| `(6)->(3,3)` | 40 | 1 | 0 | 0 | 0 | 0 |
| `(6)->(4,2)` | 15 | 2 | 4 | 2 | 4 | 60 |

It is a legal, nonnegative feature on every allowed `d=4` edge, not merely on
the three witness rows. Its full normalized divergence, in lexicographic node
order, is

```text
(0, -2, 0, -4, 24)
```

at `((2,2,2),(2,4),(3,3),(4,2),(6))`.

Under the plain pullback `Pq=q o rho`, `phi_G` is not fixed: its reflected
partner is the last block of the child on the same channel. The plain
symmetric and antisymmetric pieces are

```text
phi_+ = (phi_G + P phi_G)/2,
phi_- = (phi_G - P phi_G)/2.
```

The one-dimensional span of `phi_G` is not closed under `P`. In contrast,
under the true raw-induced action,

```text
T phi_G(e)
 = alpha(child(e)) last(child(e))
 = first(child(e))
 = phi_G(e).
```

Hence `span(phi_G)` is closed and fixed under `T`; no reflected partner is
needed for that action. Equivalently, the raw column has value `60` on each of
the two reversed root edges and zero elsewhere.

This covariance does not rescue a symmetry argument: `T` does not preserve the
target `S4`. The column is admissible as an algebraic feature, but its
one-dimensional nomination is neither uniquely selected nor sufficiently
justified by reflection symmetry for the original feasibility problem.

## 4. Witness pairing and verdict

For

```text
W = -E_(2,2,2) + 2E_(2,4) - 2E_(4,2),
```

the exact pairing is

```text
W(phi_G) = -0 + 2(-2) - 2(-4) = 4.
```

The old 156 columns pair to zero and the target pairs to `504`, so in the
`A*c=b` sign convention this row forces

```text
c_phi = 504/4 = +126.
```

The plain reflected partner pairs to `-4`, the plain symmetric part to zero,
and the plain antisymmetric part to `4`. Thus the witness escape lies entirely
in the plain-antisymmetric direction, even though `phi_G` is fixed under the
different, raw-induced action `T`.

**Verdict B.** `phi_G` is a legal, exact, nonnegative, and naturally covariant
column, but it is only an algebraic symmetry-breaking escape from this witness.
Because reversal does not preserve the original divergence target, symmetry
does not uniquely select or sufficiently justify its one-dimensional space as
a correction to the original feasibility problem. This verdict makes no claim
that a feasible flow cannot lie there; it rejects only the proposed WLOG
justification. No extended equality solve or nonnegativity search is performed
here.

`tests/test_k4_symmetry_admissibility.py` verifies every formula above exactly.
