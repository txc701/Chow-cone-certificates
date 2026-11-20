# Functional scan: which moment-type inequalities have a monotonicity certificate?

Status: exact computation for `1 <= d <= 20` (matroid ranks 2 to 21). It is finite evidence
and a finite theorem for those ranks; it is not a proof for all `d`.

## Setting

For `phi : {0..d} -> Z` and a support composition `c` of `d+2` (all parts `>= 2`),

    W_phi(c) = (d+1)! * G(c) * ( E phi(F_c) - E phi(X_d) ),

with `G(c) = U_c * prod(n_i - 1)`, `F_c = sum_i Y_i - 1` (`Y_i` independent, uniform on
`{1..n_i-1}`) the flag variable of Cheng-Lin's expansion `CH_M = sum_J N_J P_J`, and `X_d`
the Eulerian distribution of the Boolean matroid. A nonnegative flow on the support
split-DAG with divergence `W_phi` writes `E phi(X_M) <= E phi(X_d)` as a nonnegative
combination of the cover cases of Cheng-Lin Lemma 3.29. Call it a *monotonicity
certificate* for `phi`. For `phi = (2p-d)^2, (2p-d)^4` the weight is a constant multiple of
the repository's `w` and `w4` (tested node by node).

Existence is decided by exact integer max-flow. By `RESEARCH_NOTES.md` Propositions 2 and 3,
whose proofs use only that the weight vanishes off the support, a certificate exists if and
only if every ancestor-closed set of support compositions has nonnegative weight sum.

## Affine invariance

Every `F_c` and `X_d` is a probability distribution with mean `d/2`. Hence
`E alpha(F_c) = alpha(d/2) = E alpha(X_d)` for affine `alpha`, so `W_alpha = 0` and
`W_phi` depends only on the second difference
`D2 phi(a) = phi(a+1) - 2 phi(a) + phi(a-1)`, `1 <= a <= d-1`.

The code represents a second difference `lam` by the function
`sum_a lam[a] * (p-a)_+`. This representative is in general **not symmetric** in `p`, even
when `lam` is. Example: `shell_phi(4, 0)` is `(p-2)_+`, and `2(p-2)_+ = |p-2| + (p-2)`.
The mirror image differs by an affine function, so the weight is the same; the test
`test_affine_functions_have_zero_weight_so_weights_are_affine_invariant` checks this, and
that `phi + mirror(phi)`, which is symmetric, has exactly twice the weight.

## From finitely many generators to every even moment

Let `m` range over the attained values of `|2a-d|`, that is `m = d mod 2, ..., d-2` in steps
of 2, and let `tail_m` have second difference `1` where `|2a-d| >= m` and `0` elsewhere.

If `D2 phi(a) = lam(|2a-d|)` with `lam >= 0` nondecreasing, then modulo affine functions

    phi = sum_m mu_m * tail_m,     mu_m = lam(m) - lam(m-2) >= 0   (lam(m-2) := 0 at the smallest m),

because both sides have the same second difference (telescoping). For even `k`,

    D2 (p - d/2)^k (a) = 2 * sum_{j=1}^{k/2} C(k, 2j) (a - d/2)^(k-2j),

the binomial expansion of `(x+1)^k + (x-1)^k - 2x^k`: a polynomial in `(a-d/2)^2` with
nonnegative coefficients, hence nonnegative and nondecreasing in `|2a-d|`. So every even
central moment is a nonnegative combination of the `tail_m`, and certificates add.
`tail_decomposition` computes the `mu_m` and verifies the identity exactly;
`test_even_moments_decompose_nonnegatively_over_the_tail_generators` checks `k = 2..40`,
`d = 1..20`, and the closed form above.

## Results (`python3 src/run_functional_scan.py`, about 40 s)

* `tail_m`: a certificate exists for every admissible `m` and every `1 <= d <= 20`.
  Consequently, for loopless matroids of rank 2 to 21, `E phi(X_M) <= E phi(X_d)` for every
  `phi` with nonnegative, outward-nondecreasing second difference, in particular for every
  even central moment. Odd central moments vanish on both sides by symmetry. Rank 1 is
  outside the scan and trivial: the Chow polynomial is 1.
* Moments `k = 2, 4, 6, 8, 10, 12, 16, 24` were also solved directly: feasible for every
  `1 <= d <= 20`. Exponentials `x^p + x^(d-p)`, `x = 2, 3, 10`: feasible.
* Minimal peel width, `1 <= d <= 16`: 2 for `k=2`; at most 3 for `k = 4..12`; at most 4 for
  `k = 16, 24`; at most 5 for `k = 40` (`summary.json`, key `min_peel_width`).
* `shell_m` (second difference supported on `|2a-d| = m`): the innermost shell, which is the
  absolute deviation `|p - d/2|` up to a positive factor and an affine function, has **no**
  certificate for any `4 <= d <= 20`; `shell_2` also fails for even `d >= 12`.

The absolute-deviation failure means only that this family of monotonicity certificates
cannot prove `E|X_M - d/2| <= E|X_d - d/2|`. It is **not** a matroid counterexample: the
monotone cone is a relaxation of the set of flag vectors of matroids. Whether the
inequality holds for matroids is not addressed here.

All statements about matroids are conditional on Cheng-Lin's flag expansion
(Proposition 3.26) and Lemma 3.29, exactly as the `k=2` and `k=4` results are.

## Files and independent checking

    python3 src/run_functional_scan.py [DMAX] [DWIDTH] [DFLOW]   # defaults 20 16 10
    python3 src/verify_functional_scan.py [DBRUTE]               # default 8; exit status 1 on any problem
    python3 -m pytest tests/test_functional_scan.py

* `results/functional_scan/summary.json`: verdicts, deficits, minimal peel widths.
* `results/functional_scan/flows.json`: one explicit flow per feasible case with `d <= 10`
  (153 flows). `check_flow` re-verifies each without any max-flow code.
* `results/functional_scan/cuts.json`: for each of the 22 infeasible cases, generators of a
  descendant-closed set whose complement is an ancestor-closed set of negative weight.
  `check_cut` re-verifies each without any max-flow code.
* For `d <= 8` the verifier compares all 120 verdicts with a brute-force minimum over every
  ancestor-closed set.

For `11 <= d <= 20` the feasible verdicts rest on the max-flow value alone (flows are not
stored, to keep the repository small); rerun the driver with a larger `DFLOW` to store them.
