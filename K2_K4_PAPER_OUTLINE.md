# Referee-facing outline: two Chow-cone flow certificates

**Status.** Initial outline only.  The mathematical inputs are frozen at
`main` commit `65e105603c2367b8bbde3ff8eed7226e2d17a1a2` for Cheng--Lin
Conjecture 3.30 and at commit
`c92951f3cde24cb946171d66a033c4ac7f7b2ecc` for the uniform fourth-moment
certificate.  The matroid bridge is `K4_MATROID_BRIDGE.md`.

## Proposed title

**Nonnegative flows for Chow-polynomial moments of matroids**

## Main results to state in the introduction

1. **Cheng--Lin Conjecture 3.30.**  For every `d>=1`, its variance flag form
   is an explicit nonnegative combination of the normalized flag-count
   inequalities of Cheng--Lin Lemma 3.29.  The certificate uses peel-two
   support-DAG edges.
2. **Sharp fourth-central-moment theorem.**  For every loopless rank-`d+1`
   matroid,
   `E[(X_M-d/2)^4] <= E[(X_d-d/2)^4]`.  This proves the `k=4` case of
   Cheng--Lin Conjecture 3.14.
3. **Fourth-moment flag strengthening.**  The scaled fourth-moment flag form
   is itself a nonnegative combination of the same Lemma 3.29 inequalities.
   Its certificate uses peel-width at most three.
4. **Common mechanism.**  Both results follow from the same support reduction,
   composition-cover dictionary, and finite-poset principle: an upward
   nonnegative flow with the prescribed divergence is a positive combination
   certificate.

## Section plan

### 1. Introduction and statements

- Fix Cheng--Lin's loopless, standard-Chow-polynomial setting.
- State the Conjecture 3.30 theorem and the fourth-moment theorem separately.
- Explain that the second is Conjecture 3.14 at `k=4`, not another proof of
  Conjecture 3.30.
- State the stronger flag-level fourth-moment identity.

### 2. Flag expansions and support compositions

- Recall Cheng--Lin Proposition 3.26, `N_J`, `U_J`, and `P_J`.
- Give the bijection between subsets and block compositions.
- Isolate the common support factor `product_i(n_i-1)`.
- Record the cover/split dictionary, including the final-block boundary.

### 3. The finite-poset divergence principle

- Orient Boolean covers upward.
- Prove coefficientwise that `div(f)=w` implies
  `sum_J w_Jx_J=sum_e f(e)(x_tail-x_head)`.
- Apply isotonicity only after the formal identity is established.
- Separate this incidence lemma from Cheng--Lin Lemma 3.29.

### 4. The variance certificate and Conjecture 3.30

- Derive the variance weight from the flag expansion.
- Define the peel-two `G(child)` flow.
- Prove its divergence and nonnegativity uniformly.
- Deduce the identity of linear forms resolving Conjecture 3.30.

### 5. Deriving the fourth-moment weight

- Realize each nonzero `P_J/P_J(1)` as a shifted sum of independent uniform
  variables.
- Compute the common mean, variance, and fourth block moment.
- Derive `15V^2-6Q_2-12V-B_d` without treating it as definitional.
- Handle the exceptional Boolean constants at `d=1,2` explicitly.

### 6. Primitive fourth-moment divergences

- Introduce the primitive `F_2`, `F_3`, and `F_4` move-multisets.
- Prove their normalized divergence identities.
- Derive the signed flow
  `(30V(child)+30N-12)F_2+72F_3-48F_4`.

### 7. Zero-divergence rerouting

- Replace each negative peel-four move by equal-endpoint path differences.
- Treat nonfinal, final-left, and final-right moves.
- Define the final-right cascade and prove termination on `F_2` or `F_3`.
- Keep balanced move labels until aggregation.

### 8. Uniform nonnegativity and the main theorem

- Classify every possible subtraction from a fixed edge.
- Prove the cascade collision bounds and reserve inequalities.
- Treat `d=1`, `d=2`, and small block sizes separately.
- Extend by zero off support, invoke Lemma 3.29, and prove the sharp moment
  bound and its flag-level strengthening.

### 9. The shared Chow-cone mechanism

- Compare peel-two variance transport with peel-three fourth-moment transport.
- Explain what is structural (support, divergence, monotonicity) and what is
  moment-specific (primitive identities and rerouting).
- Record open directions without proposing a `k=6` or general-even-moment
  claim.

### Appendices

- Composition and factorial-ratio calculations.
- Complete collision bookkeeping and boundary tables.
- Lean correspondence for the frozen `k=2` certificate only.
- Exact computational corroboration, clearly labeled non-load-bearing.

## Referee-facing claim discipline

- Cite Cheng--Lin Proposition 3.26 and Lemma 3.29 as external inputs.
- State the global loopless convention and standard Chow polynomial at the
  outset.
- Do not infer an equality classification from the fourth-moment flow.
- Do not present bounded computations as evidence for the all-dimensional
  step.
- Do not claim a higher-even-moment pattern beyond the two proved cases.
