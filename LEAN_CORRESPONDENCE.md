# Lean ⇄ frozen-proof correspondence table

Frozen mathematical artifact: `PROOF_CONJECTURE_3_30.md` (commit `e0e64a3`)
and the referee draft `ARXIV_PROOF_DRAFT.md` (commit `dc87a7b`). The Lean
project lives in `lean/`; library name `ChowCone`. Lean toolchain v4.32.2,
mathlib pinned at tag `v4.32.2`.

Scope (per the certification mandate): the *new combinatorial core* only.
Cheng–Lin's Lemma 3.29 and everything matroid-theoretic enter solely as
**hypotheses** of the final corollaries; no Chow-ring/matroid theory is
formalized.

## Design decisions affecting fidelity (declared up front)

* **Compositions as `List ℕ`.** A support state is a list `c` with
  `∀ m ∈ c, 2 ≤ m` (`Supp c`) and `3 ≤ c.sum` (this encodes $d\ge1$ via
  $\Sigma = d+2$; Draft §7's boundary case $d=1$ is the instance
  `c = [3]`). The subset dictionary (Draft §2) identifies subsets
  $J\subseteq[d]$ with such lists; the identification itself is also
  formalized on the flow side: cover edges into a composition are indexed
  by adjacent block pairs, cover edges out of it by admissible splits.
* **Scalars in ℚ.** All quantities ($G$, $w$, $\rho$, flows) are rationals
  defined by the *verbatim* formulas with casts; no integrality claims are
  needed anywhere in the frozen proof, and none are asserted.
* **Divergence.** `div c := outSum c − inSum c` with
  `outSum c = Σ_{i<r} Σ_{p ∈ Icc 1 (c_i−1)} F c i p` (all admissible
  splits; Draft §2 notes offsets `p = c_r − 1` at the final block do not
  correspond to Boolean edges — `F` vanishes there definitionally, since
  its indicators only fire at `p = 2` or `p = c_i − 2`, and
  `c_i − 1 = c_i − 2` is impossible, so including them changes no sum) and
  `inSum c = Σ_{i<r−1} F (mergeAt c i) i (c_i)` (Draft §6: every Boolean
  cover edge into `c` merges a unique adjacent pair — Lemma 7's
  completeness — realized here as the definition of `inSum`, with the
  equivalence to "sum over all parents" proved in
  `lean/ChowCone/Main.lean` as `sum_fEdge_in`).
* **Moves vs edges, multiplicity.** `F c i p` is *defined* as
  `(indN + indFL + indFR) · G(child)` — the sum over selected moves
  realizing the edge `(c,i,p)`. The FL/FR coincidence at a final block 4
  (Draft Def. 4) is therefore handled definitionally: both indicators fire
  at the same `(i,p)` and the edge carries `2·G(child)`.

## Table

| Lean name (`ChowCone/…`) | Frozen counterpart | Statement |
|---|---|---|
| `Basic.lean : rho` | Draft Def. 3, $\rho(n)=n(n-3)/2$ | `rho m = (m*(m-3) : ℚ)/2` via casts (`(m:ℚ)*((m:ℚ)-3)/2`) |
| `Basic.lean : Supp` | Draft §2 support | all parts ≥ 2 |
| `Basic.lean : gprod, G` | Draft Def. 3 | `G c = (c.sum−1)! · last(c) · Π_i ((c_i−1)/c_i!)` |
| `Basic.lean : U, acoef` | Draft §1, $U_J$, $a_J$ | verbatim formulas in ℚ |
| `Basic.lean : w` | Draft (W) | `w c = G c · Σ_i rho c_i` |
| `Basic.lean : w_eq_U_mul_a` | Draft (W) ⇔ §1 defs | `w c = U c * acoef c` (fidelity: our `w` IS Cheng–Lin's $U_Ja_J$) |
| `Basic.lean : G_pos` | Draft Def. 3, $G>0$ | `Supp c → c ≠ [] → 0 < G c` |
| `Flow.lean : splitAt, mergeAt` | Draft §2 dictionary | block surgery on lists |
| `Flow.lean : indN, indFL, indFR, F` | Draft Def. 4 | selected-move indicators; `F = (indN+indFL+indFR)·G(child)` |
| `Flow.lean : F_nonneg` | Draft Def. 4, $f\ge0$ | `0 ≤ F c i p` |
| `Flow.lean : outSum, inSum, div` | Draft §3 divergence | as above |
| `Ratios.lean : G_split_nonfinal` | Draft Lemma 5 (N) | `G(splitAt c i 2) = rho c_i * G c` for nonfinal `c_i ≥ 4` |
| `Ratios.lean : G_split_final_left` | Draft Lemma 5 (FL) | `G(...) = (c_i−2)(c_i−3)/2 * G c` final |
| `Ratios.lean : G_split_final_right` | Draft Lemma 5 (FR) | `G(...) = (c_i−3) * G c` final |
| `Divergence.lean : outSum_eq` | Draft Cor. 6 | `outSum c = G c * Σ_{c_i≥4} rho c_i` |
| `Divergence.lean : inSum_eq` | Draft Lemma 7 | `inSum c = G c * #{i : c_i = 2}` (terminal-(2,2) multiplicity definitional, see above) |
| `Divergence.lean : div_eq_w` | Draft Thm 1 (§7), main identity | `Supp c → 3 ≤ c.sum → div c = w c` |
| `Divergence.lean : div_eq_w_all` | Draft §7 non-support nodes | `3 ≤ c.sum → div c = w c` for ALL compositions (parts ≥ 1) |
| `Main.lean : splitAt_valid_of_pos, splitAt_inversion` | Draft Lemma 7 (aliasing + completeness) | degenerate splits cannot match a composition; a valid split landing on `c` forces parent `mergeAt c i`, offset `c_i` |
| `Main.lean : fEdge, fEdge_nonneg` | Draft Def. 4 edge flow | vertex-pair flow on the Fintype `Composition n` |
| `Main.lean : sum_fEdge_out / sum_fEdge_in` | Draft §3/§6 + Lemma 7 completeness | Σ over ALL children/parents equals `outSum`/`inSum` |
| `Main.lean : fEdge_div` | Draft Thm 1 identity (D) | `Σ_u fEdge v u − Σ_u fEdge u v = w v` on `Composition n`, `n ≥ 3` |
| `Main.lean : fEdge_ne_zero_cover` | Draft §2 dictionary | nonzero flow edges are Boolean covers (one valid split) |
| `Abstract.lean : flow_identity` | Draft Lemma 2 (identity part) | `div f = w → Σ_v w v · x v = Σ_{u,v} f u v · (x u − x v)` on a Fintype |
| `Abstract.lean : flow_nonneg_combination` | Draft Lemma 2 + Thm 1 conclusion | `f ≥ 0`, monotone `x` along edges ⇒ `Σ_v w v · x v ≤ 0` |
| `Main.lean : conjecture_3_30_certificate` | Draft Thm 1/1′ | assembled: for every `n = d+2 ≥ 3`, `fEdge ≥ 0`, `div fEdge = w`, and with Lemma 3.29 as the hypothesis `hmono`, both the identity (1) and `Σ (w/U)·N ≤ 0` |

## External hypotheses (not formalized, by mandate)

* Cheng–Lin Lemma 3.29 (monotonicity of $N_J/U_J$) — enters as an explicit
  hypothesis of the final corollary.
* The interpretation of subsets-of-$[d]$ as flag types and everything
  about matroids/Chow rings.

## Verification requirements

`#print axioms` on `flowDiv_eq_w`, `flowDiv_eq_w_all`, `flow_identity`,
`flow_nonneg_combination`, `fEdge_div`, `conjecture_3_30_certificate`,
`w_eq_U_mul_a`, `fEdge_nonneg`, `F_nonneg` must show only `propext`,
`Classical.choice`, `Quot.sound` (the standard mathlib trio). No `sorry`,
no `admit`, no custom axioms, no `native_decide`.

**Status 2026-08-21: ALL VERIFIED.** Full build (mathlib v4.32.2, Lean
v4.32.2) succeeds; `grep` for sorry/admit/axiom/native_decide over
`lean/ChowCone*` is clean; the axiom audit (`lean/AxiomCheck.lean`) prints
exactly the standard trio for all nine theorems. Its exact output is preserved
in `lean/AxiomCheck.txt`. Per the certification mandate, formalization STOPS
here: Cheng–Lin's Lemma 3.29 and the matroid theory remain external hypotheses.
