/-
Abstract finite linear-form lemma (Draft Lemma 2, identity + sign parts).

Over any finite vertex type: a nonnegative flow whose divergence is `wt`
rewrites `Σ wt·x` as a nonnegative combination of edge differences, hence
`Σ wt·x ≤ 0` whenever `x` is monotone along flow-carrying edges.  With
`x = N/U` this is exactly the Cheng–Lin "nonnegative linear combination of
the monotonicity inequalities" (Lemma 3.29 enters as the hypothesis
`hmono`).
-/
import Mathlib

namespace ChowCone

variable {V : Type*} [Fintype V]

/-- Summation by parts: if `div f = wt` then `Σ_v wt v · x v` equals the
edge-difference combination (Draft Lemma 2, coefficient comparison). -/
theorem flow_identity (f : V → V → ℚ) (wt x : V → ℚ)
    (hdiv : ∀ v, (∑ u, f v u) - (∑ u, f u v) = wt v) :
    ∑ v, wt v * x v = ∑ v, ∑ u, f v u * (x v - x u) := by
  have h1 : (∑ v, ∑ u, f v u * (x v - x u))
      = (∑ v, ∑ u, f v u * x v) - (∑ v, ∑ u, f v u * x u) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have h2 : (∑ v, ∑ u, f v u * x u) = ∑ u, (∑ v, f v u) * x u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul]
  have h3 : (∑ v, ∑ u, f v u * x v) = ∑ v, (∑ u, f v u) * x v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
  rw [h1, h2, h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← hdiv v]
  ring

/-- Sign part: nonnegative flow + monotone `x` along flow edges gives
`Σ wt·x ≤ 0` (Draft Lemma 2 + Theorem 1 conclusion). -/
theorem flow_nonneg_combination (f : V → V → ℚ) (wt x : V → ℚ)
    (hdiv : ∀ v, (∑ u, f v u) - (∑ u, f u v) = wt v)
    (hf : ∀ u v, 0 ≤ f u v)
    (hmono : ∀ u v, f u v ≠ 0 → x u ≤ x v) :
    ∑ v, wt v * x v ≤ 0 := by
  rw [flow_identity f wt x hdiv]
  apply Finset.sum_nonpos
  intro v _
  apply Finset.sum_nonpos
  intro u _
  by_cases h : f v u = 0
  · rw [h]
    ring_nf
    exact le_refl 0
  · have hx := hmono v u h
    exact mul_nonpos_iff.mpr (Or.inl ⟨hf v u, by linarith⟩)

/-- Cheng–Lin form (Draft equation (1)): with `x = N/U`, the weighted sum
`Σ (wt/U)·N` is the explicit nonnegative combination of the monotonicity
differences `N u/U u − N v/U v`; in particular it is `≤ 0` under
Lemma 3.29 (hypothesis `hmono`). -/
theorem conjecture_combination (f : V → V → ℚ) (wt N U : V → ℚ)
    (hdiv : ∀ v, (∑ u, f v u) - (∑ u, f u v) = wt v)
    (hU : ∀ v, U v ≠ 0) :
    ∑ v, (wt v / U v) * N v
      = ∑ v, ∑ u, f v u * (N v / U v - N u / U u) := by
  have hx := flow_identity f wt (fun v => N v / U v) hdiv
  rw [← hx]
  refine Finset.sum_congr rfl fun v _ => ?_
  field_simp

theorem conjecture_nonpos (f : V → V → ℚ) (wt N U : V → ℚ)
    (hdiv : ∀ v, (∑ u, f v u) - (∑ u, f u v) = wt v)
    (hf : ∀ u v, 0 ≤ f u v)
    (hU : ∀ v, U v ≠ 0)
    (hmono : ∀ u v, f u v ≠ 0 → N u / U u ≤ N v / U v) :
    ∑ v, (wt v / U v) * N v ≤ 0 := by
  have h := flow_nonneg_combination f wt (fun v => N v / U v) hdiv hf hmono
  calc ∑ v, (wt v / U v) * N v
      = ∑ v, wt v * (N v / U v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        field_simp
    _ ≤ 0 := h

end ChowCone
