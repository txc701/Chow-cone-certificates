# Branch B — the fourth-moment (k=4) analogue

**Status: discovery work.** Nothing here affects the frozen k=2 proof of
Conjecture 3.30 (main branch, commit `e0e64a3`, Lean-certified `131daca`).
All computations exact integers; reproduce with `python3 src/run_k4.py` and
the snippet in `results/k4_peel_thresholds.json`'s generator.

## Derivation

From Cheng–Lin's flag decomposition ($P_J(x)=\frac1x\prod f_{n_i}(x)$,
every $F_J$ has mean $d/2$), the fourth-central-moment analogue of the
Corollary 3.28 coefficient is (scaled by 720 to clear denominators)

$$w^{(4)}_J = U_J\prod_i(n_i-1)\cdot S_4,\qquad
S_4 = 3\sum_i n_i(n_i-2)(3n_i^2-6n_i-4)
+30\sum_{i<j}n_in_j(n_i-2)(n_j-2) - 720\,\mu_4(X_d),$$

using $\operatorname{var}(Y)=n(n-2)/12$, $\mu_4(Y)=n(n-2)(3n^2-6n-4)/240$
for a uniform block, and independence
($\mu_4(\sum Y_i)=\sum\mu_4+6\sum_{i<j}\sigma_i^2\sigma_j^2$).
$\sum_J w^{(4)}_J=0$ holds identically because the Boolean matroid realizes
$N_J=U_J$. Same support ($\prod(n_i-1)$ factor), same split-DAG machinery.

## Findings (exact, ranges as stated)

1. **Boolean fourth moment is only eventually polynomial.**
   $\mu_4(X_d)=(d+2)(5d+8)/240$ for $d\ge3$, but $\mu_4=1/16$ at $d=1$ and
   $1/3$ at $d=2$ — genuine exceptions (1-dependence boundary effect). The
   $k=2$ analogue has **no** such anomaly ($\operatorname{var}=(d+2)/12$
   for all $d$). Weights use the exact per-$d$ Eulerian value.

2. **NEW CONJECTURE (k=4 analogue of Conjecture 3.30).** The
   divergence-$w^{(4)}$ flow is **feasible for every $d\le20$**: the
   fourth-moment flag inequality $\sum_J a^{(4)}_JN_J\le0$ appears to be a
   nonnegative combination of the *same* monotonicity inequalities
   (Lemma 3.29). Via the flag decomposition this would prove
   $E[(X_M-d/2)^4]\le\mu_4(X_d)$ for every matroid of rank $d+1$: the
   Boolean matroid maximizes the fourth central moment.

3. **The k=2 structure deforms, it does not survive.**
   * Staircase identities: only the trivial ones ($\sigma_4(T_0)=
     \sigma_4(T_1)=0$, both equal to the global sum) hold; every deeper
     staircase has strictly **positive** slack (e.g. $d=4$:
     $\sigma_4(T_2)=5760$). The tight-ideal chain is gone.
   * Shell sums are nonzero with **mixed signs** (e.g. $d=7$: shell 3
     $=-967680$, shell 5 $=+193536$, residual $=+774144$), so every $k=4$
     certificate must carry flow **across** shells — the forced
     decomposition is a variance-only phenomenon.
   * **peel2 dies** (first infeasible at $d=4$; sporadic feasibility at
     $d\in\{2,3,5\}$ only). `largest_block` dies at $d=13$ (vs 15 for k=2).

4. **NEW MECHANISM: peel-width threshold.** Allowing splits with
   $\min(p,n_i-p)\le t$: $t=2$ dies at $d=4$; $t=3$ (and above) is
   **feasible for all tested $d\le16$**. Together with k=2 (where $t=2$
   suffices) this suggests:

   > **Conjecture (peel-width).** The $2t$-th central-moment flag
   > inequality admits a monotonicity certificate supported on splits of
   > peel width $\le t+1$.

5. **Interpretation for the k=2 proof.** The explicit $G$-certificate's
   telescoping ($\rho(m)$ ratios, staircase parity argument) is tied to
   the specific quadratic $\rho(n)=n(n-3)/2$; the $k=4$ weights involve
   quartic block data plus genuine cross-terms $\sigma_i^2\sigma_j^2$, and
   correspondingly need wider peels and shell-crossing flows. A uniform
   $k=4$ certificate, if it exists, should be sought on the peel-$\le3$
   DAG, presumably with flows depending on (block, peel size, cross-term
   prefix data) rather than a single $G$-type product.

## Failed ideas (k=4)

* peel2-only certificates (dead at $d=4$);
* hoping the staircase/shell decomposition transfers (it provably cannot:
  the tight ideals are simply not tight for $w^{(4)}$).

## Next steps (future sessions)

* Feasibility beyond $d=20$ (cheap; same machinery).
* Extract peel-$\le3$ certificates for small $d$ and hunt for a
  two-parameter ratio formula generalizing $G$.
* Decide whether Cheng–Lin's §3.2 CMFS machinery yields
  $E[(X_M-d/2)^4]\le\mu_4(X_d)$ directly for $d\ge$ some bound, which
  would make the flag-level conjecture the sharp combinatorial refinement.
