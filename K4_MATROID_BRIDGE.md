# The matroid-theoretic meaning of the uniform `k=4` certificate

**Frozen combinatorial input.** Commit
`c92951f3cde24cb946171d66a033c4ac7f7b2ecc` proves the uniform
peel-width-three flow theorem used below.  Nothing in this document changes or
re-audits that certificate.  Cheng--Lin's pinned source is
`paper/cheng-lin-v3.pdf`; all matroids in that paper are assumed loopless, and
`CH_M` denotes the standard (not augmented) Chow polynomial.

**Verdict: FULL MATROID THEOREM.**  The frozen flow, Cheng--Lin's flag
expansion, and Cheng--Lin Lemma 3.29 prove the fourth-moment case of their
Conjecture 3.14 for every loopless matroid in their original setting.  No new
matroid-theoretic reduction is required.

## 1. Exact theorem

Let `M` be a loopless matroid of rank `d+1`, where `d>=1`, and write

```text
CH_M(x)=sum_(p=0)^d h_p(M)x^p,
Pr(X_M=p)=h_p(M)/CH_M(1).
```

Let `X_d` be Cheng--Lin's random variable for the Boolean matroid on `d+1`
elements; equivalently, it is the descent statistic on the symmetric group
`S_(d+1)`.  Then

```text
E[(X_M-d/2)^4] <= E[(X_d-d/2)^4]
                  { 1/16,                    d=1,
                = { 1/3,                     d=2,
                  { (d+2)(5d+8)/240,         d>=3.
```

Thus the Boolean matroid gives a sharp upper bound.  This is precisely the
`k=4` instance of Cheng--Lin Conjecture 3.14.  The proof gives the following
strictly stronger flag-level statement, analogous to their Conjecture 3.30.

For `J={j_1<...<j_m}` contained in `[d]`, put `j_0=0`, `r=m+1`, and

```text
n_i=j_i-j_(i-1)       (1<=i<=m),
n_r=d+2-j_m.
```

For `J` empty, this convention means `r=1` and `n_1=d+2`.  Cheng--Lin write
the flag sum over proper subsets; adjoining `J=[d]` is harmless because its
composition has a part equal to `1`, so its flag polynomial and every
coefficient below vanish.

Let `N_J=N_J(M)` be the number of flags of flats of rank type `J`, and let

```text
U_J=N_J(Boolean)=n_r(d+1)! / product_i n_i!.
```

Set

```text
v_i=n_i(n_i-2),       V_J=sum_i v_i,       Q_(2,J)=sum_i v_i^2,
B_d=720 E[(X_d-d/2)^4],
a_J^(4)=product_i(n_i-1) [15V_J^2-6Q_(2,J)-12V_J-B_d],
w_J^(4)=U_J a_J^(4).
```

There are explicit coefficients `f_d(J,J')>=0`, nonzero only on Boolean
cover pairs `J'=J union {j}`, such that the following is an identity of
linear forms in the variables `(N_K)_(K subseteq [d])`:

```text
sum_J a_J^(4) N_J
 = sum_(J lessdot J') f_d(J,J')
     [N_J/U_J-N_(J')/U_(J')].                         (1)
```

The coefficients in (1) are exactly the frozen uniform flow.  In particular,
the fourth-moment flag inequality is a nonnegative linear combination of the
same normalized flag-count inequalities used in Conjecture 3.30.

The `k=2` statement proved in the frozen Cheng--Lin branch is Conjecture 3.30
itself.  The theorem above should be called the `k=4` case of Conjecture 3.14,
or a fourth-moment strengthening in the style of Conjecture 3.30, rather than
being called Conjecture 3.30.

## 2. Derivation of the fourth-moment coefficient

This section derives the displayed formula for `a_J^(4)` from the Chow
polynomial; it is not adopted as a definition without justification.

### 2.1 The flag summands

Cheng--Lin Proposition 3.26 (p. 20 of the pinned v3 manuscript) gives

```text
CH_M(x)=sum_(J subseteq [d]) N_J P_J(x),
P_J(x)=x^(-1) product_i f_(n_i)(x),
f_n(x)=x+x^2+...+x^(n-1).                              (2)
```

Consequently

```text
P_J(1)=product_i(n_i-1).                               (3)
```

If some `n_i=1`, then `f_(n_i)=0`, so `P_J=0`; both sides of every
coefficient identity below vanish because of the factor `product_i(n_i-1)`.
No probability variable attached to that zero polynomial is needed.  We may
therefore derive the nonzero coefficient on the support `n_i>=2`.

On this support, let `Y_i` be independent and uniform on
`{1,...,n_i-1}`.  Dividing (2) by (3) shows that the formal random variable
with probability generating function `P_J(x)/P_J(1)` is

```text
F_J=sum_i Y_i-1.                                      (4)
```

Since `E[Y_i]=n_i/2` and `sum_i n_i=d+2`, every flag summand has the same
mean:

```text
E[F_J]=sum_i n_i/2-1=d/2.                             (5)
```

This common mean is what permits a central moment of the Chow-polynomial
mixture to be computed term by term.

### 2.2 Exact block moments

Put `Z_i=Y_i-n_i/2` and `v_i=n_i(n_i-2)`.  Direct evaluation of the finite
uniform sums gives

```text
E[Z_i]=0,
E[Z_i^2]=v_i/12,
E[Z_i^4]=v_i(3n_i^2-6n_i-4)/240.                      (6)
```

The variables `Z_i` are independent and centered.  In the fourth power of
their sum, terms with an odd exponent have expectation zero, so

```text
E[(F_J-d/2)^4]
 = sum_i E[Z_i^4]+6 sum_(i<j) E[Z_i^2]E[Z_j^2].       (7)
```

Multiplying (7) by `720` and substituting (6) yields, line by line,

```text
720 E[(F_J-d/2)^4]
 = 3 sum_i v_i(3n_i^2-6n_i-4)
     +30 sum_(i<j) v_i v_j                            (8)
 = 3 sum_i v_i(3v_i-4)+30 sum_(i<j) v_i v_j           (9)
 = 9Q_(2,J)-12V_J+15(V_J^2-Q_(2,J))                 (10)
 = 15V_J^2-6Q_(2,J)-12V_J.                           (11)
```

Here (9) uses `n_i^2-2n_i=v_i`, while (10) uses
`2 sum_(i<j)v_i v_j=V_J^2-Q_(2,J)`.

### 2.3 Subtracting the Boolean fourth moment

Normalize (2) at `x=1`.  Equations (4)--(5) give

```text
CH_M(1) E[(X_M-d/2)^4]
 = sum_J N_J P_J(1) E[(F_J-d/2)^4],                  (12)
CH_M(1)=sum_J N_J P_J(1).                            (13)
```

Let `beta_d=E[(X_d-d/2)^4]` and `B_d=720 beta_d`.  Subtract `beta_d`
times (13) from (12), multiply by `720`, and use (3) and (11):

```text
720 CH_M(1) [E[(X_M-d/2)^4]-beta_d]
 = sum_J N_J product_i(n_i-1)
     [15V_J^2-6Q_(2,J)-12V_J-B_d]                   (14)
 = sum_J a_J^(4) N_J.                                (15)
```

Thus the fourth-moment flag coefficient is derived from Cheng--Lin's flag
decomposition.  It is not an independently imposed weight.

For the Boolean variable, Cheng--Lin Corollary 3.13 (pp. 13--14) gives

```text
beta_d=(d+2)(5d+8)/240       for d>=3.
```

The two smaller Eulerian polynomials are `1+x` and `1+4x+x^2`, giving
`beta_1=1/16` and `beta_2=1/3`.  Therefore, with `N=d+2`,

```text
B_1=45,       B_2=240,
B_d=3(d+2)(5d+8)=15N^2-6N       for d>=3.             (16)
```

Finally, multiplying the coefficient in (15) by Cheng--Lin's Boolean flag
count gives

```text
w_J^(4)=U_J a_J^(4)
       =G(c(J))[15V_J^2-6Q_(2,J)-12V_J-B_d],          (17)
G(c)=U_J product_i(n_i-1)
    =(d+1)! n_r product_i ((n_i-1)/n_i!).             (18)
```

Equations (17)--(18) identify exactly the divergence target proved at the
frozen checkpoint.  Setting `M` equal to the Boolean matroid in (14) also
derives the conservation law `sum_J w_J^(4)=0`.

## 3. From the frozen flow to the matroid inequality

The subset/composition dictionary sends a Boolean cover
`J -> J union {j}` to a split of one composition block.  Every edge used by
the frozen certificate is such a legal cover edge; its endpoints stay on the
support.  Extend the flow by zero to all other Boolean covers.  The frozen
theorem states, for every `K subseteq [d]`,

```text
f_d>=0,       div(f_d)(K)=w_K^(4),                    (19)
```

where divergence is outflow minus inflow.

Set `x_J=N_J/U_J`.  Finite summation by parts, or simply collecting the
coefficient of each `x_K`, gives

```text
sum_J a_J^(4)N_J
 =sum_J w_J^(4)x_J
 =sum_(J lessdot J') f_d(J,J')[x_J-x_(J')].           (20)
```

Equation (20) is formal.  It depends only on (19) and does not yet use any
matroid inequality.  It is exactly the linear-form identity (1).

For an actual loopless matroid, Cheng--Lin Lemma 3.29 supplies the sole sign
input:

```text
J subseteq J'  implies  N_J/U_J <= N_(J')/U_(J').     (21)
```

Every bracket on the right of (20) is therefore nonpositive, while every
`f_d(J,J')` is nonnegative.  Hence `sum_J a_J^(4)N_J<=0`.  Combining this
with (14), and using `CH_M(1)>0` (indeed its constant Chow coefficient is
one), proves

```text
E[(X_M-d/2)^4] <= beta_d.
```

This completes the bridge from the abstract flow to the stated theorem for
matroids.

## 4. Dependency table

| Input | Exact role | Classification |
|---|---|---|
| Cheng--Lin's global convention (p. 2) and Definition 3.1 (p. 8) | `M` is loopless; defines the standard Chow polynomial, `X_M`, and `X_d` | External notation and scope |
| Cheng--Lin Notation 3.25 and Proposition 3.26 (p. 20) | Gives the block composition and flag expansion (2), hence (3), (12), and (13) | External matroid theorem, based there on the Feichtner--Yuzvinsky flag basis |
| Cheng--Lin's formula for `U_J=N_J(Boolean)` (p. 21) | Identifies (17)--(18) with the frozen composition weight | External established formula |
| Boolean Chow polynomial/Eulerian distribution and Cheng--Lin Corollary 3.13 (pp. 13--14) | Gives (16); `d=1,2` are direct Eulerian calculations | External standard input plus elementary boundary calculation |
| Uniform-block moment calculation | Gives (4)--(11) | Elementary exact algebra in this bridge |
| Frozen commit `c92951f` | Supplies the legal nonnegative all-`d` flow and the divergence identity (19), including `d=1,2` | Previously proved combinatorial theorem |
| Finite-poset summation by parts | Gives the equality (20) from (19) | Formal incidence algebra; no matroid theory |
| Cheng--Lin Lemma 3.29 (p. 22) | Gives the sign (21) for actual flag counts | External matroid theorem; sole input in the final sign step |
| A new matroid-theoretic reduction | Not needed | None |

The semi-small/CMFS induction of Cheng--Lin Theorem 3.3 is not used in this
proof.  Their flag expansion and monotonicity lemma already place the frozen
flow in the original matroid setting.

## 5. Scope and claim discipline

The verdict is **FULL MATROID THEOREM**, not **CONDITIONAL THEOREM** and not
**COMBINATORIAL CERTIFICATE ONLY**.

The scope is exactly the standard Chow polynomial of every loopless matroid
of rank `d+1`, `d>=1`, as in Cheng--Lin.  There is no realizability, field, or
simplicity hypothesis.  The result does not presently include an equality
classification, the augmented Chow polynomial, higher even moments, or a
general `k=2m` theorem.  The proof is symbolic and all-dimensional; the saved
finite computations corroborate the certificate but are not logical inputs.

The referee-facing organization prompted by this completed bridge is recorded
separately in `K2_K4_PAPER_OUTLINE.md`.
