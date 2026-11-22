/-
The uniform fourth-moment flow for every `d ≥ 1` (Theorem 9.1).

Manuscript of 21 November 2026: Section 7, "All surviving flow is supported
on peel-two and peel-three cover edges"; Section 9, the boundary dimensions
`d = 1, 2` with `B_1 = 45`, `B_2 = 240` (equation (18)), and Theorem 9.1.

Scope.  This file proves Theorem 9.1 in positional coordinates: for every
`d ≥ 1` the flow is nonnegative, its divergence is `w^{(4)}` at every
composition of `N = d + 2` (on and off the support), and every edge that
carries flow splits a block `n ↦ (p, n-p)` with `min(p, n-p) ≤ 3`.  The
vertex form on `Composition (d+2)` and the inequality under Cheng and Lin's
Lemma 3.29 are in `ChowCone.K4.Certificate`.
-/
import ChowCone.K4.Nonnegativity

namespace ChowCone
namespace K4

open Finset

/-! ### Exact cancellation of the `F_4` occurrences -/

lemma LeftSource.eAB_injective : Function.Injective LeftSource.eAB := by
  rintro ⟨P, t, S⟩ ⟨P', t', S'⟩ h
  simp only [LeftSource.eAB, PEdge.mk.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq] at h3
  obtain ⟨rfl, h4, rfl⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

lemma Source.eAB_injective : Function.Injective Source.eAB := by
  rintro ⟨P, t⟩ ⟨P', t'⟩ h
  simp only [Source.eAB, PEdge.mk.injEq] at h
  obtain ⟨h1, h2, h5⟩ := h
  obtain ⟨rfl, -⟩ := List.append_inj h1 h2
  subst h5
  rfl

theorem LAB_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LAB N c i p ≤ 48 * G (splitAt c i p) * (indNs 4 c i p + indFLs 4 c i p) := by
  rw [LAB_apply]
  refine sum_key_le _ _ _ _ _ (fun s _ s' _ h => LeftSource.eAB_injective h) ?_ ?_
  · nlinarith [indNs_mul_G_nonneg (by norm_num : 2 ≤ 4) c i p,
      indFLs_mul_G_nonneg (by norm_num : 2 ≤ 4) c i p]
  · rintro ⟨P, t, S⟩ hs hk
    obtain ⟨hP, hS, ht, -⟩ := mem_leftSources.1 hs
    simp only at hP hS ht
    simp only [LeftSource.eAB, PEdge.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have hsupp : Supp (P ++ (t + 4) :: S) := supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, hS⟩⟩
    have e : t + 4 - 4 = t := by omega
    rw [LeftSource.rawDebit, LeftSource.occ_child]
    show 48 * G (P ++ 4 :: t :: S) ≤ _
    rw [splitAt_append, e]
    by_cases hS' : S = []
    · subst hS'
      rw [indNs_append_nil, indFLs_append 4 P (t + 4) hsupp (by omega)]
      apply le_of_eq
      ring
    · rw [indNs_append 4 P S (t + 4) hsupp hS' (by omega),
        indFLs_append_of_ne 4 P S (t + 4) 4 hS']
      apply le_of_eq
      ring

theorem RAB_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RAB N c i p ≤ 48 * G (splitAt c i p) * indFRs 4 c i p := by
  rw [RAB_apply]
  refine sum_key_le _ _ _ _ _ (fun s _ s' _ h => Source.eAB_injective h) ?_ ?_
  · nlinarith [indFRs_mul_G_nonneg (by norm_num : 2 ≤ 4) c i p]
  · rintro ⟨P, t⟩ hs hk
    obtain ⟨hP, ht, -⟩ := mem_rightSources.1 hs
    simp only at hP ht
    simp only [Source.eAB, PEdge.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have hsupp : Supp (P ++ [t + 4]) := supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, supp_nil⟩⟩
    have e1 : t + 4 - 4 = t := by omega
    have e2 : t + 4 - t = 4 := by omega
    have h1 := indFRs_append 4 P (t + 4) hsupp (by omega)
    rw [e1] at h1
    rw [Source.rawDebit, Source.occ_child]
    show 48 * G (P ++ [t, 4]) ≤ _
    rw [splitAt_append, e2, h1]
    apply le_of_eq
    ring

/-- The corrections put exactly `48 G(child)` on the edge of every `F_4`
occurrence: the negative `F_4` terms of `f_0` are cancelled exactly. -/
theorem LAB_add_RAB (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) :
    LAB N c i p + RAB N c i p = 48 * ind 4 c i p * G (splitAt c i p) := by
  have h1 := le_antisymm (LAB_le N c i p) (LAB_ge N c i p hN)
  have h2 := le_antisymm (RAB_le N c i p) (RAB_ge N c i p hN)
  rw [h1, h2]
  unfold ind
  ring

/-- `f_d` on an edge, with the `F_4` occurrences cancelled: the reserves of
the `F_2` and `F_3` occurrences, plus the additions, minus the charges of
rows 1–6. -/
theorem fd_apply_cancelled (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) :
    fd N c i p =
      (ind 2 c i p * (30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12) + ind 3 c i p * 72)
          * G (splitAt c i p)
        + LBD N c i p + RBD N c i p + RPOS N c i p
        - LAC N c i p - LCD N c i p - RAC N c i p - RCH N c i p := by
  rw [fd_apply, f0_eq]
  linear_combination LAB_add_RAB N c i p hN

/-! ### The surviving flow is on peel-two and peel-three edges -/

lemma ind_eq_zero_of_off (s : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ s)
    (hq : c.getD i 0 - p ≠ s) : ind s c i p = 0 := by
  unfold ind indNs indFLs indFRs
  rw [if_neg (fun h => hp h.2.2.1), if_neg (fun h => hp h.2.2.1), if_neg (fun h => hq (by
    have h1 := h.2.2.1
    have h2 := h.2.2.2
    omega))]
  ring

lemma indNs_eq_zero_of_off (s : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ s) : indNs s c i p = 0 := by
  unfold indNs
  rw [if_neg (fun h => hp h.2.2.1)]

lemma indFLs_eq_zero_of_off (s : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ s) :
    indFLs s c i p = 0 := by
  unfold indFLs
  rw [if_neg (fun h => hp h.2.2.1)]

lemma indFRs_eq_zero_of_off (s : ℕ) (c : List ℕ) (i p : ℕ) (hq : c.getD i 0 - p ≠ s) :
    indFRs s c i p = 0 := by
  unfold indFRs
  rw [if_neg (fun h => hq (by
    have h1 := h.2.2.1
    have h2 := h.2.2.2
    omega))]

lemma posFlow_eq_zero (Q : List ℕ) (y : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ 2) :
    posFlow Q y c i p = 0 := by
  induction Q, y using posFlow.induct with
  | case1 => rw [posFlow]; rfl
  | case2 => rw [posFlow]; rfl
  | case3 => rw [posFlow]; rfl
  | case4 => rw [posFlow]; rfl
  | case5 Q y ih =>
    rw [posFlow]
    show edgeUnit (cYW Q (y + 4)) c i p + posFlow (Q ++ [2]) (y + 2) c i p = 0
    rw [ih, add_zero, edgeUnit_apply, if_neg]
    intro h
    exact hp (congrArg PEdge.off h).symm

lemma chargeFlow_nonneg (l : List Charge) (c : List ℕ) (i p : ℕ) : 0 ≤ chargeFlow l c i p := by
  induction l with
  | nil => exact le_refl 0
  | cons a l ih =>
    rw [chargeFlow_cons]
    exact add_nonneg (edgeUnit_nonneg _ _ _ _) ih

lemma LAC_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ LAC N c i p := by
  rw [LAC_apply]
  exact sum_key_nonneg _ _ _ _ fun s hs => s.rawDebit_nonneg N (mem_leftSources.1 hs)

lemma LCD_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ LCD N c i p := by
  rw [LCD_apply]
  exact sum_key_nonneg _ _ _ _ fun s hs => s.rawDebit_nonneg N (mem_leftSources.1 hs)

lemma RAC_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ RAC N c i p := by
  rw [RAC_apply]
  exact sum_key_nonneg _ _ _ _ fun s hs => s.rawDebit_nonneg N (mem_rightSources.1 hs)

lemma RCH_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ RCH N c i p := by
  rw [RCH_apply]
  exact sum_nonneg fun s hs =>
    mul_nonneg (s.rawDebit_nonneg N (mem_rightSources.1 hs)) (chargeFlow_nonneg _ _ _ _)

lemma LBD_eq_zero (N : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ 2) : LBD N c i p = 0 := by
  rw [LBD_apply]
  refine sum_eq_zero fun s _ => ?_
  rw [if_neg (fun h => hp (congrArg PEdge.off h).symm), mul_zero]

lemma RBD_eq_zero (N : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ 2) : RBD N c i p = 0 := by
  rw [RBD_apply]
  refine sum_eq_zero fun s _ => ?_
  rw [if_neg (fun h => hp (congrArg PEdge.off h).symm), mul_zero]

lemma RPOS_eq_zero (N : ℕ) (c : List ℕ) (i p : ℕ) (hp : p ≠ 2) : RPOS N c i p = 0 := by
  rw [RPOS_apply]
  refine sum_eq_zero fun s _ => ?_
  rw [posFlow_eq_zero _ _ _ _ _ hp, mul_zero]

/-- **The surviving flow is on peel-two and peel-three edges.**  If both
parts of the split are at least 4, the edge carries no flow. -/
theorem fd_eq_zero_of_wide (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) (hp : 4 ≤ p)
    (hq : 4 ≤ c.getD i 0 - p) : fd N c i p = 0 := by
  have h2 : ind 2 c i p = 0 := ind_eq_zero_of_off 2 c i p (by omega) (by omega)
  have h3 : ind 3 c i p = 0 := ind_eq_zero_of_off 3 c i p (by omega) (by omega)
  have hLAC : LAC N c i p = 0 := by
    have h := LAC_le N c i p
    rw [indNs_eq_zero_of_off 2 c i p (by omega), indFLs_eq_zero_of_off 2 c i p (by omega)] at h
    have h' := LAC_nonneg N c i p
    linarith
  have hLCD : LCD N c i p = 0 := by
    have h := LCD_le N c i p
    rw [indNs_eq_zero_of_off 2 c i p (by omega), indFLs_eq_zero_of_off 2 c i p (by omega)] at h
    have h' := LCD_nonneg N c i p
    linarith
  have hRAC : RAC N c i p = 0 := by
    have h := RAC_le N c i p
    rw [indFRs_eq_zero_of_off 2 c i p (by omega)] at h
    have h' := RAC_nonneg N c i p
    linarith
  have hRCH : RCH N c i p = 0 := by
    have h := RCH_le N c i p
    rw [indNs_eq_zero_of_off 2 c i p (by omega), indNs_eq_zero_of_off 3 c i p (by omega)] at h
    have h' := RCH_nonneg N c i p
    linarith
  rw [fd_apply_cancelled N c i p hN, h2, h3, hLAC, hLCD, hRAC, hRCH,
    LBD_eq_zero N c i p (by omega), RBD_eq_zero N c i p (by omega),
    RPOS_eq_zero N c i p (by omega)]
  ring

/-! ### The divergence of `f_0` at compositions off the support -/

lemma ind_eq_zero_of_not (s : ℕ) (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ)
    (hc : ¬(Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p)) : ind s c i p = 0 := by
  unfold ind indNs indFLs indFRs
  rw [if_neg (fun h => hc ⟨h.1, by have := h.2.2.1; omega, by
      have h1 := h.2.2.1
      have h2 := h.2.2.2
      omega⟩),
    if_neg (fun h => hc ⟨h.1, by have := h.2.2.1; omega, by
      have h1 := h.2.2.1
      have h2 := h.2.2.2
      omega⟩),
    if_neg (fun h => hc ⟨h.1, by
      have h1 := h.2.2.1
      have h2 := h.2.2.2
      omega, by
      have h1 := h.2.2.1
      have h2 := h.2.2.2
      omega⟩)]
  ring

lemma f0_eq_zero_of_not (c : List ℕ) (i p : ℕ)
    (hc : ¬(Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p)) : f0 c i p = 0 := by
  rw [f0_eq, ind_eq_zero_of_not 2 (by norm_num) c i p hc,
    ind_eq_zero_of_not 3 (by norm_num) c i p hc, ind_eq_zero_of_not 4 (by norm_num) c i p hc]
  ring

lemma divOf_f0_of_not_supp (c : List ℕ) (hs : ¬ Supp c) : divOf f0 c = 0 := by
  have hout : outSumOf f0 c = 0 := by
    unfold outSumOf
    exact sum_eq_zero fun i _ => sum_eq_zero fun p _ =>
      f0_eq_zero_of_not c i p (fun h => hs h.1)
  have hin : inSumOf f0 c = 0 := by
    unfold inSumOf
    refine sum_eq_zero fun i hi => f0_eq_zero_of_not _ _ _ (fun h => hs ?_)
    have hlt : i + 1 < c.length := by
      have := mem_range.1 hi
      omega
    have := Supp_splitAt (mergeAt c i) i (c.getD i 0) h.1 h.2.1 h.2.2
    rwa [splitAt_mergeAt c i hlt] at this
  unfold divOf
  rw [hout, hin, sub_zero]

lemma one_mem_of_not_supp (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (hs : ¬ Supp c) : 1 ∈ c := by
  by_contra hone
  apply hs
  intro m hm
  have := h1 m hm
  by_contra hlt
  have hm1 : m = 1 := by omega
  rw [hm1] at hm
  exact hone hm

/-- Proposition 6.3 at every composition of `N ≥ 5` with positive parts, on
and off the support. -/
theorem divOf_f0_all (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (h5 : 5 ≤ c.sum) :
    divOf f0 c = w4 c := by
  by_cases hs : Supp c
  · exact divOf_f0 c hs h5
  · rw [divOf_f0_of_not_supp c hs]
    unfold w4
    rw [G_eq_zero_of_one_mem c (one_mem_of_not_supp c h1 hs), zero_mul]

/-! ### The flow lives on the support DAG

The manuscript's flow is defined on the support DAG: its vertices are the
support compositions and its edges split a block into two parts at least 2.
In Lean a flow is a function of every positional edge `(c, i, p)`, and the
divergence sums over every offset `1 ≤ p ≤ c_i - 1`.  The lemmas below show
that `f_d` vanishes on every positional edge that is not an edge of the
support DAG, so the two descriptions agree.  They were first proved in probes
of the review of release `v1.1` (`RELEASE_CHECKS.md`). -/

/-- `(c, i, p)` is an edge of the support DAG: `c` is a support composition
and the split leaves two parts at least 2, so the child is a support
composition as well. -/
abbrev SuppEdge (c : List ℕ) (i p : ℕ) : Prop := Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p

lemma indNs_eq_zero_of_not (s : ℕ) (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ)
    (h : ¬ SuppEdge c i p) : indNs s c i p = 0 := by
  rcases indNs_cases s c i p with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨hsupp, -, hp, hm⟩ := indNs_eq_one h1
    exact h ⟨hsupp, by omega, by omega⟩

lemma indFLs_eq_zero_of_not (s : ℕ) (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ)
    (h : ¬ SuppEdge c i p) : indFLs s c i p = 0 := by
  rcases indFLs_cases s c i p with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨hsupp, -, hp, hm⟩ := indFLs_eq_one h1
    exact h ⟨hsupp, by omega, by omega⟩

lemma indFRs_eq_zero_of_not (s : ℕ) (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ)
    (h : ¬ SuppEdge c i p) : indFRs s c i p = 0 := by
  rcases indFRs_cases s c i p with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨hsupp, -, hp, hm⟩ := indFRs_eq_one h1
    exact h ⟨hsupp, by omega, by omega⟩

/-- Row 1 charges nothing off the support DAG. -/
lemma LAC_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    LAC N c i p = 0 := by
  have h1 := LAC_le N c i p
  rw [indNs_eq_zero_of_not 2 (by norm_num) c i p h,
    indFLs_eq_zero_of_not 2 (by norm_num) c i p h] at h1
  have h2 := LAC_nonneg N c i p
  simp only [zero_mul, add_zero] at h1
  linarith

/-- Row 2 charges nothing off the support DAG. -/
lemma LCD_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    LCD N c i p = 0 := by
  have h1 := LCD_le N c i p
  rw [indNs_eq_zero_of_not 2 (by norm_num) c i p h,
    indFLs_eq_zero_of_not 2 (by norm_num) c i p h] at h1
  have h2 := LCD_nonneg N c i p
  simp only [zero_mul, add_zero] at h1
  linarith

/-- Row 3 charges nothing off the support DAG. -/
lemma RAC_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    RAC N c i p = 0 := by
  have h1 := RAC_le N c i p
  rw [indFRs_eq_zero_of_not 2 (by norm_num) c i p h] at h1
  have h2 := RAC_nonneg N c i p
  simp only [zero_mul] at h1
  linarith

/-- Rows 4–6 charge nothing off the support DAG. -/
lemma RCH_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    RCH N c i p = 0 := by
  have h1 := RCH_le N c i p
  rw [indNs_eq_zero_of_not 2 (by norm_num) c i p h,
    indNs_eq_zero_of_not 3 (by norm_num) c i p h] at h1
  have h2 := RCH_nonneg N c i p
  simp only [zero_mul, add_zero] at h1
  linarith

lemma LBD_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    LBD N c i p = 0 := by
  rw [LBD_apply]
  refine sum_eq_zero fun s hs => ?_
  rw [if_neg, mul_zero]
  intro he
  apply h
  obtain ⟨P, t, S⟩ := s
  obtain ⟨hP, hS, ht, -⟩ := mem_leftSources.1 hs
  simp only at hP hS ht
  simp only [LeftSource.eBD, PEdge.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨supp_append.2 ⟨hP, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨ht, hS⟩⟩⟩, le_refl 2, ?_⟩
  rw [getD_append_length]

lemma RBD_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    RBD N c i p = 0 := by
  rw [RBD_apply]
  refine sum_eq_zero fun s hs => ?_
  rw [if_neg, mul_zero]
  intro he
  apply h
  obtain ⟨P, t⟩ := s
  obtain ⟨hP, ht, -⟩ := mem_rightSources.1 hs
  simp only at hP ht
  simp only [Source.eBD, PEdge.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  refine ⟨supp_append.2 ⟨hP, supp_cons.2 ⟨ht, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩,
    le_refl 2, ?_⟩
  rw [getD_append_length_succ']

lemma posFlow_eq_zero_of_not (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (c : List ℕ) (i p : ℕ)
    (h : ¬ SuppEdge c i p) : posFlow Q y c i p = 0 := by
  induction Q, y using posFlow.induct with
  | case1 => rw [posFlow]; rfl
  | case2 => rw [posFlow]; rfl
  | case3 => rw [posFlow]; rfl
  | case4 => rw [posFlow]; rfl
  | case5 Q y ih =>
    rw [posFlow]
    show edgeUnit (cYW Q (y + 4)) c i p + posFlow (Q ++ [2]) (y + 2) c i p = 0
    rw [ih (supp_append.2 ⟨hQ, supp_cons.2 ⟨le_refl 2, supp_nil⟩⟩), add_zero, edgeUnit_apply,
      if_neg]
    intro he
    apply h
    simp only [cYW, sqY, PEdge.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    refine ⟨supp_append.2 ⟨hQ, supp_cons.2 ⟨by omega, supp_cons.2 ⟨le_refl 2,
      supp_cons.2 ⟨le_refl 2, supp_nil⟩⟩⟩⟩, le_refl 2, ?_⟩
    rw [getD_append_length]
    omega

lemma RPOS_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ SuppEdge c i p) :
    RPOS N c i p = 0 := by
  rw [RPOS_apply]
  refine sum_eq_zero fun s hs => ?_
  rw [posFlow_eq_zero_of_not s.P s.t (mem_rightSources.1 hs).1 c i p h, mul_zero]

/-- `f_d` vanishes on every positional edge that is not an edge of the
support DAG. -/
theorem fd_eq_zero_of_not (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N)
    (h : ¬ SuppEdge c i p) : fd N c i p = 0 := by
  rw [fd_apply_cancelled N c i p hN, ind_eq_zero_of_not 2 (by norm_num) c i p h,
    ind_eq_zero_of_not 3 (by norm_num) c i p h, LBD_eq_zero_of_not N c i p h,
    RBD_eq_zero_of_not N c i p h, RPOS_eq_zero_of_not N c i p h, LAC_eq_zero_of_not N c i p h,
    LCD_eq_zero_of_not N c i p h, RAC_eq_zero_of_not N c i p h, RCH_eq_zero_of_not N c i p h]
  ring

/-! ### The boundary dimensions `d = 1, 2` and the flow for every `d` -/

/-- `B_d = 720 β_d` (equation (18)): `B_1 = 45`, `B_2 = 240`, and
`B_d = 15N^2 - 6N` for `d ≥ 3`, `N = d + 2`. -/
def Bd (d : ℕ) : ℚ :=
  if d = 1 then 45 else if d = 2 then 240
  else 15 * ((d + 2 : ℕ) : ℚ) ^ 2 - 6 * ((d + 2 : ℕ) : ℚ)

/-- `S_4 = 15V^2 - 6Q_2 - 12V - B_d` (equation (21)), for every `d`. -/
def S4d (d : ℕ) (c : List ℕ) : ℚ := 15 * V c ^ 2 - 6 * Q2 c - 12 * V c - Bd d

/-- The target `w^{(4)} = G S_4`, for every `d`. -/
def w4d (d : ℕ) (c : List ℕ) : ℚ := G c * S4d d c

/-- The coefficient `a^{(4)} = Π(n_i - 1) · S_4` (equation (20)), for every `d`. -/
def a4d (d : ℕ) (c : List ℕ) : ℚ := (c.map partQ).prod * S4d d c

theorem w4d_eq_U_mul_a4d (d : ℕ) (c : List ℕ) : w4d d c = U c * a4d d c := by
  unfold w4d U a4d G
  rw [gprod_eq_div]
  have h := factprod_ne_zero c
  field_simp

theorem w4d_eq_w4 (d : ℕ) (hd : 3 ≤ d) (c : List ℕ) (hN : c.sum = d + 2) : w4d d c = w4 c := by
  unfold w4d w4 S4d S4 Bd
  rw [if_neg (by omega), if_neg (by omega), hN]

/-- The flow of Theorem 9.1: zero for `d = 1`, raw flow `720` on
`(4) → (2,2)` for `d = 2`, and `f_d` for `d ≥ 3`. -/
noncomputable def fdAll (d : ℕ) : EdgeFlow :=
  if d = 1 then 0
  else if d = 2 then (720 : ℚ) • edgeUnit ⟨[4], 0, 2⟩
  else fd (d + 2)

lemma supp_sum_three (c : List ℕ) (hs : Supp c) (h : c.sum = 3) : c = [3] := by
  match c, hs, h with
  | [], _, h => simp at h
  | [a], _, h =>
    simp at h
    rw [h]
  | a :: b :: l, hs, h =>
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    simp only [List.sum_cons] at h
    omega

lemma supp_sum_four (c : List ℕ) (hs : Supp c) (h : c.sum = 4) : c = [4] ∨ c = [2, 2] := by
  match c, hs, h with
  | [], _, h => simp at h
  | [a], _, h =>
    simp at h
    rw [h]
    exact Or.inl rfl
  | [a, b], hs, h =>
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    simp only [List.sum_cons, List.sum_nil] at h
    have h1 : a = 2 := by omega
    have h2 : b = 2 := by omega
    rw [h1, h2]
    exact Or.inr rfl
  | a :: b :: x :: l, hs, h =>
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hx := hs x (by simp)
    simp only [List.sum_cons] at h
    omega

lemma G_four : G [4] = 3 := by
  norm_num [G, gprod, blockTerm, partQ, factQ, lastPart, Nat.factorial]

lemma G_two_two : G [2, 2] = 3 := by
  norm_num [G, gprod, blockTerm, partQ, factQ, lastPart, Nat.factorial]

/-- `d = 1`: `w^{(4)}` vanishes on the compositions of 3. -/
theorem w4d_one (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (hN : c.sum = 3) : w4d 1 c = 0 := by
  by_cases hs : Supp c
  · rw [supp_sum_three c hs hN]
    norm_num [w4d, S4d, Bd, V, Q2, vq]
  · unfold w4d
    rw [G_eq_zero_of_one_mem c (one_mem_of_not_supp c h1 hs), zero_mul]

/-- `d = 2`: the single edge `(4) → (2,2)` with raw flow `720`. -/
theorem divOf_fdAll_two (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (hN : c.sum = 4) :
    divOf (fdAll 2) c = w4d 2 c := by
  have hv : (⟨[4], 0, 2⟩ : PEdge).Valid := ⟨by decide, by decide, by decide⟩
  have hdiv : divOf (fdAll 2) c
      = 720 * ((if c = [4] then 1 else 0) - (if c = [2, 2] then 1 else 0)) := by
    unfold fdAll
    rw [if_neg (by decide), if_pos rfl, divOf_smul, divOf_edgeUnit _ hv]
    rfl
  rw [hdiv]
  by_cases hs : Supp c
  · rcases supp_sum_four c hs hN with rfl | rfl
    · rw [if_pos rfl, if_neg (by decide)]
      unfold w4d
      rw [G_four]
      norm_num [S4d, Bd, V, Q2, vq]
    · rw [if_neg (by decide), if_pos rfl]
      unfold w4d
      rw [G_two_two]
      norm_num [S4d, Bd, V, Q2, vq]
  · have hne1 : c ≠ [4] := by
      rintro rfl
      exact hs (by decide)
    have hne2 : c ≠ [2, 2] := by
      rintro rfl
      exact hs (by decide)
    rw [if_neg hne1, if_neg hne2]
    unfold w4d
    rw [G_eq_zero_of_one_mem c (one_mem_of_not_supp c h1 hs)]
    ring

/-! ### Theorem 9.1 -/

/-- Divergence, for every `d ≥ 1`, at every composition of `N = d + 2` with
positive parts. -/
theorem divOf_fdAll (d : ℕ) (hd : 1 ≤ d) (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m)
    (hN : c.sum = d + 2) : divOf (fdAll d) c = w4d d c := by
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · have h12 : d = 1 ∨ d = 2 := by omega
    rcases h12 with rfl | rfl
    · rw [w4d_one c h1 hN]
      unfold fdAll
      rw [if_pos rfl, divOf_zero]
    · exact divOf_fdAll_two c h1 hN
  · rw [w4d_eq_w4 d hge c hN]
    unfold fdAll
    rw [if_neg (by omega), if_neg (by omega), divOf_fd_eq_divOf_f0]
    exact divOf_f0_all c h1 (by omega)

/-- Nonnegativity, for every `d ≥ 1`. -/
theorem fdAll_nonneg (d : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = d + 2) :
    0 ≤ fdAll d c i p := by
  unfold fdAll
  split_ifs with h1 h2
  · exact le_refl 0
  · exact mul_nonneg (by norm_num) (edgeUnit_nonneg _ _ _ _)
  · exact fd_nonneg (d + 2) c i p hN

/-- **The flow of Theorem 9.1 is a flow on the support DAG.**  An edge of a
composition of `d + 2` that carries flow has a support parent and splits a
block into two parts at least 2. -/
theorem fdAll_ne_zero_suppEdge (d : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = d + 2)
    (h : fdAll d c i p ≠ 0) : SuppEdge c i p := by
  by_contra hg
  apply h
  unfold fdAll
  split_ifs with h1 h2
  · rfl
  · show (720 : ℚ) * edgeUnit ⟨[4], 0, 2⟩ c i p = 0
    rw [edgeUnit_apply, if_neg, mul_zero]
    intro he
    apply hg
    simp only [PEdge.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨by decide, by decide, by decide⟩
  · exact fd_eq_zero_of_not (d + 2) c i p hN hg

/-- Both ends of an edge that carries flow are support compositions. -/
theorem fdAll_ne_zero_supp (d : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = d + 2)
    (h : fdAll d c i p ≠ 0) : Supp c ∧ Supp (splitAt c i p) := by
  obtain ⟨hs, hp, hq⟩ := fdAll_ne_zero_suppEdge d c i p hN h
  exact ⟨hs, Supp_splitAt c i p hs hp hq⟩

/-- The outflow of the flow only involves the offsets `2 ≤ p ≤ n_i - 2`, the
out-edges of the support DAG.  In particular the split of the final block
that leaves a final part 1, which the Lean divergence allows and Section 2
of the manuscript excludes, carries no flow. -/
theorem outSumOf_fdAll_suppEdges (d : ℕ) (c : List ℕ) (hN : c.sum = d + 2) :
    outSumOf (fdAll d) c
      = ∑ i ∈ range c.length, ∑ p ∈ Icc 2 (c.getD i 0 - 2), fdAll d c i p := by
  unfold outSumOf
  refine sum_congr rfl fun i _ => ?_
  symm
  refine sum_subset ?_ ?_
  · intro p hp
    rw [mem_Icc] at hp ⊢
    omega
  · intro p hp hnp
    by_contra hne
    obtain ⟨-, h2, h3⟩ := fdAll_ne_zero_suppEdge d c i p hN hne
    apply hnp
    rw [mem_Icc] at hp ⊢
    omega

/-- The divergence identity of Theorem 9.1 with the edges of the support DAG
only: out-edges with both parts at least 2, and in-edges from the merges of
adjacent blocks. -/
theorem divOf_fdAll_suppEdges (d : ℕ) (hd : 1 ≤ d) (c : List ℕ) (hs : Supp c)
    (hN : c.sum = d + 2) :
    (∑ i ∈ range c.length, ∑ p ∈ Icc 2 (c.getD i 0 - 2), fdAll d c i p)
        - inSumOf (fdAll d) c = w4d d c := by
  rw [← outSumOf_fdAll_suppEdges d c hN]
  exact divOf_fdAll d hd c (fun m hm => by have := hs m hm; omega) hN

/-- Every edge that carries flow splits a block as `n ↦ (p, n-p)` with
`min(p, n-p) ≤ 3`. -/
theorem fdAll_used_edge (d : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = d + 2)
    (h : fdAll d c i p ≠ 0) : p ≤ 3 ∨ c.getD i 0 - p ≤ 3 := by
  unfold fdAll at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  · left
    by_contra hp
    apply h
    show (720 : ℚ) * edgeUnit ⟨[4], 0, 2⟩ c i p = 0
    rw [edgeUnit_apply, if_neg, mul_zero]
    intro he
    have := congrArg PEdge.off he
    simp at this
    omega
  · by_contra hwide
    exact h (fd_eq_zero_of_wide (d + 2) c i p hN (by omega) (by omega))

/-- **Theorem 9.1 (uniform fourth-moment flow).**  For every `d ≥ 1`, the
flow is nonnegative on the compositions of `N = d + 2`; its divergence is
`w^{(4)}` at every composition of `N` with positive parts, in particular at
every support state; and every edge that carries flow is an edge of the
support DAG (a support composition, split into two parts at least 2) and
splits a block with `min(p, n-p) ≤ 3`. -/
theorem uniform_fourth_moment_flow (d : ℕ) (hd : 1 ≤ d) :
    (∀ (c : List ℕ) (i p : ℕ), c.sum = d + 2 → 0 ≤ fdAll d c i p) ∧
    (∀ c : List ℕ, (∀ m ∈ c, 1 ≤ m) → c.sum = d + 2 → divOf (fdAll d) c = w4d d c) ∧
    (∀ (c : List ℕ) (i p : ℕ), c.sum = d + 2 → fdAll d c i p ≠ 0 →
      SuppEdge c i p ∧ (p ≤ 3 ∨ c.getD i 0 - p ≤ 3)) :=
  ⟨fun c i p hN => fdAll_nonneg d c i p hN,
    fun c h1 hN => divOf_fdAll d hd c h1 hN,
    fun c i p hN h => ⟨fdAll_ne_zero_suppEdge d c i p hN h, fdAll_used_edge d c i p hN h⟩⟩

end K4
end ChowCone
