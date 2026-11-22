/-
The signed fourth-moment flow `f_0` and its divergence.

Manuscript of 21 November 2026: Section 5, equation (21) (the target
`w^{(4)} = G S_4`); Section 6, equation (22) (`τ_2, τ_3, τ_4`), Lemma 6.1
(primitive divergences), Lemma 6.2 (discrete product rule), equations
(25)–(26), and Proposition 6.3 (`div f_0 = w^{(4)}` for `d ≥ 3`).

Scope.  This file defines the primitive move multisets `F_s`, the flow
`F_{2,V}` and the signed flow `f_0` in the positional coordinates of the
`k = 2` files, and proves the three statements above.  It does not treat
the rerouting of Section 7 (the flow `f_d`), nonnegativity, the cases
`d = 1, 2`, the derivation of `S_4` from moments in Section 5, or the
matroid bridge.
-/
import ChowCone.Main
import ChowCone.K4.CascadeSizes

namespace ChowCone
namespace K4

open Finset

/-! ### Positional edge flows and their divergence -/

/-- A flow in positional coordinates: `f c i p` is the total flow on the
edge that splits block `i` of `c` at offset `p`. -/
abbrev EdgeFlow := List ℕ → ℕ → ℕ → ℚ

/-- Total outflow of `c`: the sum over all splits, as `outSum` of
`ChowCone.Flow`. -/
def outSumOf (f : EdgeFlow) (c : List ℕ) : ℚ :=
  ∑ i ∈ range c.length, ∑ p ∈ Icc 1 (c.getD i 0 - 1), f c i p

/-- Total inflow of `c`: the sum over the adjacent pairs of blocks of `c`,
as `inSum` of `ChowCone.Flow`. -/
def inSumOf (f : EdgeFlow) (c : List ℕ) : ℚ :=
  ∑ i ∈ range (c.length - 1), f (mergeAt c i) i (c.getD i 0)

/-- Divergence: outflow minus inflow. -/
def divOf (f : EdgeFlow) (c : List ℕ) : ℚ := outSumOf f c - inSumOf f c

/-- For the `k = 2` flow `F` this is the divergence `flowDiv` of
`ChowCone.Flow`. -/
theorem divOf_F (c : List ℕ) : divOf F c = flowDiv c := rfl

/-! ### The primitive move multisets `F_s` -/

/-- Indicator of the selected move of `F_s` on a nonfinal block:
`m ↦ (s, m-s)` for `m ≥ s+2`. -/
def indNs (s : ℕ) (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 < c.length ∧ p = s ∧ s + 2 ≤ c.getD i 0 then 1 else 0

/-- Indicator of the final-left move `m ↦ (s, m-s)`, final block `m ≥ s+2`. -/
def indFLs (s : ℕ) (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 = c.length ∧ p = s ∧ s + 2 ≤ c.getD i 0 then 1 else 0

/-- Indicator of the final-right move `m ↦ (m-s, s)`, final block `m ≥ s+2`. -/
def indFRs (s : ℕ) (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 = c.length ∧ p = c.getD i 0 - s ∧ s + 2 ≤ c.getD i 0 then 1 else 0

/-- The number of selected occurrences of `F_s` on the edge `(c, i, p)`.
It is `2` when the two final labels give the same balanced edge. -/
def ind (s : ℕ) (c : List ℕ) (i p : ℕ) : ℚ :=
  indNs s c i p + indFLs s c i p + indFRs s c i p

/-- The flow that gives every selected occurrence of `F_s` the raw flow
`φ(child) · G(child)`. -/
def wprim (s : ℕ) (φ : List ℕ → ℚ) : EdgeFlow := fun c i p =>
  ind s c i p * (φ (splitAt c i p) * G (splitAt c i p))

/-- The primitive flow `F_s`: raw flow `G(child)` on every selected
occurrence (Section 6). -/
def prim (s : ℕ) : EdgeFlow := wprim s fun _ => 1

/-- `F_2` is the peel-two flow `F` of the `k = 2` files. -/
theorem prim_two : prim 2 = F := by
  funext c i p
  simp [prim, wprim, ind, indNs, indFLs, indFRs, F, indN, indFL, indFR]

lemma ite_one_zero_eq_one_iff (P : Prop) [Decidable P] :
    (if P then (1 : ℚ) else 0) = 1 ↔ P := by
  split_ifs with h <;> simp [h]

/-- The indicators are the indicators of the tagged selected occurrences
of `ChowCone.K4.CascadeOrigins`. -/
theorem indNs_eq_one_iff (s : ℕ) (hs : 2 ≤ s ∧ s ≤ 4) (c : List ℕ) (i p : ℕ) :
    indNs s c i p = 1 ↔
      (⟨s, .nonfinal, c, i⟩ : Occ).Selected ∧ (⟨s, .nonfinal, c, i⟩ : Occ).offset = p := by
  unfold indNs
  rw [ite_one_zero_eq_one_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨hs, h1, h4, h2⟩, h3.symm⟩
  · rintro ⟨⟨-, h1, h4, h2⟩, h3⟩
    exact ⟨h1, h2, h3.symm, h4⟩

theorem indFLs_eq_one_iff (s : ℕ) (hs : 2 ≤ s ∧ s ≤ 4) (c : List ℕ) (i p : ℕ) :
    indFLs s c i p = 1 ↔
      (⟨s, .finalLeft, c, i⟩ : Occ).Selected ∧ (⟨s, .finalLeft, c, i⟩ : Occ).offset = p := by
  unfold indFLs
  rw [ite_one_zero_eq_one_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨hs, h1, h4, h2⟩, h3.symm⟩
  · rintro ⟨⟨-, h1, h4, h2⟩, h3⟩
    exact ⟨h1, h2, h3.symm, h4⟩

theorem indFRs_eq_one_iff (s : ℕ) (hs : 2 ≤ s ∧ s ≤ 4) (c : List ℕ) (i p : ℕ) :
    indFRs s c i p = 1 ↔
      (⟨s, .finalRight, c, i⟩ : Occ).Selected ∧ (⟨s, .finalRight, c, i⟩ : Occ).offset = p := by
  unfold indFRs
  rw [ite_one_zero_eq_one_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨hs, h1, h4, h2⟩, h3.symm⟩
  · rintro ⟨⟨-, h1, h4, h2⟩, h3⟩
    exact ⟨h1, h2, h3.symm, h4⟩

/-! ### The ratios `G(child)/G(parent)` -/

/-- `τ_s(m) = ρ₀(s) ρ₀(m-s) / ρ₀(m)`, the ratio `G(child)/G(parent)` of a
nonfinal split `m ↦ (s, m-s)`; it equals
`binom(m,s) (s-1)(m-s-1)/(m-1)`.  Closed forms for `s = 2, 3, 4` are
`tau_two`, `tau_three`, `tau_four`. -/
def tau (s m : ℕ) : ℚ := blockTerm s * blockTerm (m - s) / blockTerm m

lemma tau_mul (s m : ℕ) (hm : 2 ≤ m) :
    tau s m * blockTerm m = blockTerm s * blockTerm (m - s) := by
  unfold tau
  exact div_mul_cancel₀ _ (blockTerm_ne_zero m hm)

/-- Nonfinal split, abstract form. -/
lemma G_ratio_N' (s : ℕ) (l₁ l₂ : List ℕ) (m : ℕ) (hm : 2 ≤ m) (hsm : s ≤ m)
    (h2 : l₂ ≠ []) :
    G (l₁ ++ s :: (m - s) :: l₂) = tau s m * G (l₁ ++ m :: l₂) := by
  unfold G
  have hsum : (l₁ ++ s :: (m - s) :: l₂).sum = (l₁ ++ m :: l₂).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast : lastPart (l₁ ++ s :: (m - s) :: l₂) = lastPart (l₁ ++ m :: l₂) := by
    rw [lastPart_append_cons_of_ne _ _ _ (by simp),
        lastPart_append_cons_of_ne _ _ _ h2]
    rw [show ((m - s) :: l₂ : List ℕ) = [] ++ (m - s) :: l₂ from rfl,
        lastPart_append_cons_of_ne _ _ _ h2]
  rw [hlast]
  have hg : gprod (l₁ ++ s :: (m - s) :: l₂)
      = gprod l₁ * (blockTerm s * blockTerm (m - s)) * gprod l₂ := by
    rw [gprod_append, gprod_cons, gprod_cons]
    ring
  have hg' : gprod (l₁ ++ m :: l₂) = gprod l₁ * blockTerm m * gprod l₂ := by
    rw [gprod_append, gprod_cons]
    ring
  rw [hg, hg', ← tau_mul s m hm]
  ring

/-- Final split, left orientation, abstract form: the final factor changes
by `(m-s)/m`. -/
lemma G_ratio_FL' (s : ℕ) (l₁ : List ℕ) (m : ℕ) (hm : 2 ≤ m) (hsm : s ≤ m) :
    G (l₁ ++ [s, m - s]) = tau s m * (((m : ℚ) - s) / m) * G (l₁ ++ [m]) := by
  unfold G
  have hsum : (l₁ ++ [s, m - s]).sum = (l₁ ++ [m]).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast1 : lastPart (l₁ ++ [s, m - s]) = m - s := lastPart_append_pair _ _ _
  have hlast2 : lastPart (l₁ ++ [m]) = m := lastPart_append_cons_nil l₁ m
  rw [hlast1, hlast2]
  have hg : gprod (l₁ ++ [s, m - s]) = gprod l₁ * (blockTerm s * blockTerm (m - s)) := by
    rw [gprod_append, gprod_cons, gprod_cons, gprod_nil]
    ring
  have hg' : gprod (l₁ ++ [m]) = gprod l₁ * blockTerm m := by
    rw [gprod_append, gprod_cons, gprod_nil]
    ring
  rw [hg, hg', ← tau_mul s m hm, Nat.cast_sub hsm]
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : ((m : ℚ) - s) / m * m = (m : ℚ) - s := div_mul_cancel₀ _ hm0
  linear_combination
    (-((Nat.factorial ((l₁ ++ [m]).sum - 1) : ℚ) * gprod l₁ * tau s m * blockTerm m)) * key

/-- Final split, right orientation, abstract form: the final factor changes
by `s/m`. -/
lemma G_ratio_FR' (s : ℕ) (l₁ : List ℕ) (m : ℕ) (hm : 2 ≤ m) (hsm : s ≤ m) :
    G (l₁ ++ [m - s, s]) = tau s m * ((s : ℚ) / m) * G (l₁ ++ [m]) := by
  unfold G
  have hsum : (l₁ ++ [m - s, s]).sum = (l₁ ++ [m]).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast1 : lastPart (l₁ ++ [m - s, s]) = s := lastPart_append_pair _ _ _
  have hlast2 : lastPart (l₁ ++ [m]) = m := lastPart_append_cons_nil l₁ m
  rw [hlast1, hlast2]
  have hg : gprod (l₁ ++ [m - s, s]) = gprod l₁ * (blockTerm s * blockTerm (m - s)) := by
    rw [gprod_append, gprod_cons, gprod_cons, gprod_nil]
    ring
  have hg' : gprod (l₁ ++ [m]) = gprod l₁ * blockTerm m := by
    rw [gprod_append, gprod_cons, gprod_nil]
    ring
  rw [hg, hg', ← tau_mul s m hm]
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : (s : ℚ) / m * m = (s : ℚ) := div_mul_cancel₀ _ hm0
  linear_combination
    (-((Nat.factorial ((l₁ ++ [m]).sum - 1) : ℚ) * gprod l₁ * tau s m * blockTerm m)) * key

/-- Nonfinal split, positional form. -/
lemma G_splitAt_nonfinal' (s : ℕ) (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length)
    (hm : 2 ≤ c.getD i 0) (hsm : s ≤ c.getD i 0) :
    G (splitAt c i s) = tau s (c.getD i 0) * G c := by
  have hlt : i < c.length := Nat.lt_of_succ_lt hi
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.1 h
    omega
  rw [splitAt_eq]
  set m := c.getD i 0 with hm'
  conv_rhs => rw [hd]
  exact G_ratio_N' s (c.take i) (c.drop (i + 1)) m hm hsm hdrop

lemma G_splitAt_final_left' (s : ℕ) (c : List ℕ) (i : ℕ) (hi : i + 1 = c.length)
    (hm : 2 ≤ c.getD i 0) (hsm : s ≤ c.getD i 0) :
    G (splitAt c i s)
      = tau s (c.getD i 0) * (((c.getD i 0 : ℚ) - s) / c.getD i 0) * G c := by
  have hlt : i < c.length := by omega
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) = [] := by
    apply List.drop_eq_nil_iff.2
    omega
  rw [splitAt_eq, hdrop]
  set m := c.getD i 0 with hm'
  conv_rhs => rw [hd, hdrop]
  exact G_ratio_FL' s (c.take i) m hm hsm

lemma G_splitAt_final_right' (s : ℕ) (c : List ℕ) (i : ℕ) (hi : i + 1 = c.length)
    (hm : 2 ≤ c.getD i 0) (hsm : s ≤ c.getD i 0) :
    G (splitAt c i (c.getD i 0 - s))
      = tau s (c.getD i 0) * ((s : ℚ) / c.getD i 0) * G c := by
  have hlt : i < c.length := by omega
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) = [] := by
    apply List.drop_eq_nil_iff.2
    omega
  have hsub : c.getD i 0 - (c.getD i 0 - s) = s := by omega
  rw [splitAt_eq, hdrop, hsub]
  set m := c.getD i 0 with hm'
  conv_rhs => rw [hd, hdrop]
  exact G_ratio_FR' s (c.take i) m hm hsm

/-! ### Outflow of a weighted primitive flow -/

lemma ind_small (s : ℕ) (c : List ℕ) (i p : ℕ) (h : ¬ s + 2 ≤ c.getD i 0) :
    ind s c i p = 0 := by
  unfold ind indNs indFLs indFRs
  rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
  ring

lemma ind_nonfinal (s : ℕ) (c : List ℕ) (i p : ℕ) (hs : Supp c)
    (hi : i + 1 < c.length) (h : s + 2 ≤ c.getD i 0) :
    ind s c i p = if p = s then 1 else 0 := by
  have hne : ¬ (i + 1 = c.length) := by omega
  have h1 : indNs s c i p = if p = s then 1 else 0 := by
    unfold indNs
    by_cases hp : p = s
    · rw [if_pos hp, if_pos]
      exact ⟨hs, hi, hp, h⟩
    · rw [if_neg hp, if_neg]
      exact fun h' => hp h'.2.2.1
  have h2 : indFLs s c i p = 0 := by
    unfold indFLs
    rw [if_neg]
    exact fun h' => hne h'.2.1
  have h3 : indFRs s c i p = 0 := by
    unfold indFRs
    rw [if_neg]
    exact fun h' => hne h'.2.1
  unfold ind
  rw [h1, h2, h3]
  ring

lemma ind_final (s : ℕ) (c : List ℕ) (i p : ℕ) (hs : Supp c)
    (hi : i + 1 = c.length) (h : s + 2 ≤ c.getD i 0) :
    ind s c i p = (if p = s then 1 else 0) + (if p = c.getD i 0 - s then 1 else 0) := by
  have hnl : ¬ (i + 1 < c.length) := by omega
  have h1 : indNs s c i p = 0 := by
    unfold indNs
    rw [if_neg]
    exact fun h' => hnl h'.2.1
  have h2 : indFLs s c i p = if p = s then 1 else 0 := by
    unfold indFLs
    by_cases hp : p = s
    · rw [if_pos hp, if_pos]
      exact ⟨hs, hi, hp, h⟩
    · rw [if_neg hp, if_neg]
      exact fun h' => hp h'.2.2.1
  have h3 : indFRs s c i p = if p = c.getD i 0 - s then 1 else 0 := by
    unfold indFRs
    by_cases hp : p = c.getD i 0 - s
    · rw [if_pos hp, if_pos]
      exact ⟨hs, hi, hp, h⟩
    · rw [if_neg hp, if_neg]
      exact fun h' => hp h'.2.2.1
  unfold ind
  rw [h1, h2, h3]
  ring

/-- Per-block outflow.  The weight `φ` is assumed to take the same value on
the two children of a final block `m ≥ s + 2`, that is on `(.., s, m-s)` and
`(.., m-s, s)`. -/
lemma sum_p_wprim (s : ℕ) (hs1 : 1 ≤ s) (φ : List ℕ → ℚ) (c : List ℕ) (i : ℕ)
    (hs : Supp c) (hi : i < c.length)
    (hsym : i + 1 = c.length → s + 2 ≤ c.getD i 0 →
      φ (splitAt c i (c.getD i 0 - s)) = φ (splitAt c i s)) :
    ∑ p ∈ Icc 1 (c.getD i 0 - 1), wprim s φ c i p
      = G c * (if s + 2 ≤ c.getD i 0 then tau s (c.getD i 0) * φ (splitAt c i s) else 0) := by
  by_cases h : s + 2 ≤ c.getD i 0
  · rw [if_pos h]
    have hmem : s ∈ Icc 1 (c.getD i 0 - 1) := mem_Icc.2 ⟨hs1, by omega⟩
    have hmemr : c.getD i 0 - s ∈ Icc 1 (c.getD i 0 - 1) := mem_Icc.2 ⟨by omega, by omega⟩
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt | heq
    · have hstep : ∀ p ∈ Icc 1 (c.getD i 0 - 1), wprim s φ c i p
          = if p = s then φ (splitAt c i s) * G (splitAt c i s) else 0 := by
        intro p _
        unfold wprim
        rw [ind_nonfinal s c i p hs hlt h]
        by_cases hp : p = s
        · subst hp
          rw [if_pos rfl, if_pos rfl, one_mul]
        · rw [if_neg hp, if_neg hp, zero_mul]
      rw [sum_congr rfl hstep,
        sum_ite_eq' (Icc 1 (c.getD i 0 - 1)) s (fun _ => φ (splitAt c i s) * G (splitAt c i s)),
        if_pos hmem, G_splitAt_nonfinal' s c i hlt (by omega) (by omega)]
      ring
    · have hstep : ∀ p ∈ Icc 1 (c.getD i 0 - 1), wprim s φ c i p
          = (if p = s then φ (splitAt c i s) * G (splitAt c i s) else 0)
            + (if p = c.getD i 0 - s then
                φ (splitAt c i (c.getD i 0 - s)) * G (splitAt c i (c.getD i 0 - s)) else 0) := by
        intro p _
        unfold wprim
        rw [ind_final s c i p hs heq h, add_mul]
        congr 1
        · by_cases hp : p = s
          · subst hp
            rw [if_pos rfl, if_pos rfl, one_mul]
          · rw [if_neg hp, if_neg hp, zero_mul]
        · by_cases hp : p = c.getD i 0 - s
          · subst hp
            rw [if_pos rfl, if_pos rfl, one_mul]
          · rw [if_neg hp, if_neg hp, zero_mul]
      have hm0 : (c.getD i 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [sum_congr rfl hstep, sum_add_distrib,
        sum_ite_eq' (Icc 1 (c.getD i 0 - 1)) s (fun _ => φ (splitAt c i s) * G (splitAt c i s)),
        sum_ite_eq' (Icc 1 (c.getD i 0 - 1)) (c.getD i 0 - s)
          (fun _ => φ (splitAt c i (c.getD i 0 - s)) * G (splitAt c i (c.getD i 0 - s))),
        if_pos hmem, if_pos hmemr, hsym heq h,
        G_splitAt_final_left' s c i heq (by omega) (by omega),
        G_splitAt_final_right' s c i heq (by omega) (by omega)]
      field_simp
      ring
  · rw [if_neg h, sum_congr rfl fun p _ => by unfold wprim; rw [ind_small s c i p h, zero_mul]]
    simp

lemma outSumOf_wprim (s : ℕ) (hs1 : 1 ≤ s) (φ : List ℕ → ℚ) (c : List ℕ) (hs : Supp c)
    (hsym : ∀ i, i + 1 = c.length → s + 2 ≤ c.getD i 0 →
      φ (splitAt c i (c.getD i 0 - s)) = φ (splitAt c i s)) :
    outSumOf (wprim s φ) c = G c * ∑ i ∈ range c.length,
      (if s + 2 ≤ c.getD i 0 then tau s (c.getD i 0) * φ (splitAt c i s) else 0) := by
  unfold outSumOf
  rw [mul_sum]
  exact sum_congr rfl fun i hi => sum_p_wprim s hs1 φ c i hs (mem_range.1 hi) (hsym i)

/-! ### Inflow of a weighted primitive flow -/

/-- The selected occurrences of `F_s` on the edge that merges the blocks
`i`, `i+1` of `c`: one if block `i` equals `s`, and one more if block `i+1`
is final and equals `s`. -/
lemma ind_merge (s : ℕ) (c : List ℕ) (i : ℕ) (hs : Supp c) (hi : i + 1 < c.length) :
    ind s (mergeAt c i) i (c.getD i 0)
      = (if c.getD i 0 = s then 1 else 0)
        + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = s then 1 else 0) := by
  have hq : Supp (mergeAt c i) := Supp_mergeAt c i hi hs
  have hlen : (mergeAt c i).length = c.length - 1 := mergeAt_length c i hi
  have hget : (mergeAt c i).getD i 0 = c.getD i 0 + c.getD (i + 1) 0 := mergeAt_getD c i hi
  have hb := hs _ (getD_mem c (i + 1) hi)
  have ha := hs _ (getD_mem c i (by omega))
  unfold ind indNs indFLs indFRs
  simp only [hget, hlen, hq, true_and]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma wprim_merge (s : ℕ) (φ : List ℕ → ℚ) (c : List ℕ) (i : ℕ) (hs : Supp c)
    (hi : i + 1 < c.length) :
    wprim s φ (mergeAt c i) i (c.getD i 0)
      = G c * φ c * ((if c.getD i 0 = s then 1 else 0)
          + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = s then 1 else 0)) := by
  unfold wprim
  rw [splitAt_mergeAt c i hi, ind_merge s c i hs hi]
  ring

/-- Total inflow: every block equal to `s` has exactly one incoming selected
occurrence, with raw flow `φ(c) G(c)`.  The sole-block composition `(s)` is
excluded. -/
lemma inSumOf_wprim (s : ℕ) (φ : List ℕ → ℚ) (c : List ℕ) (hs : Supp c) (hne : c ≠ [s]) :
    inSumOf (wprim s φ) c
      = G c * φ c * ∑ i ∈ range c.length, (if c.getD i 0 = s then 1 else 0) := by
  unfold inSumOf
  rcases hlen : c.length with _ | n
  · simp
  rcases n with _ | k
  · have hc : c = [c.getD 0 0] := by
      have h0 : (0 : ℕ) < c.length := by omega
      have hd := decomp_at c 0 h0
      have hdrop : c.drop 1 = [] := by
        apply List.drop_eq_nil_iff.2
        omega
      rw [hdrop] at hd
      simpa using hd
    have hns : ¬ c.getD 0 0 = s := by
      intro h
      apply hne
      rw [hc, h]
    show (∑ i ∈ range 0, wprim s φ (mergeAt c i) i (c.getD i 0))
      = G c * φ c * ∑ i ∈ range 1, (if c.getD i 0 = s then (1 : ℚ) else 0)
    rw [range_zero, sum_empty, range_one, sum_singleton, if_neg hns, mul_zero]
  · have hstep : ∀ i ∈ range (k + 1),
        wprim s φ (mergeAt c i) i (c.getD i 0)
          = G c * φ c * ((if c.getD i 0 = s then 1 else 0)
              + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = s then 1 else 0)) := by
      intro i hi
      exact wprim_merge s φ c i hs (by
        have := mem_range.1 hi
        omega)
    rw [show k + 1 + 1 - 1 = k + 1 from rfl, sum_congr rfl hstep, ← mul_sum]
    congr 1
    rw [sum_add_distrib]
    have hres : ∀ i ∈ range (k + 1),
        (if i + 2 = c.length ∧ c.getD (i + 1) 0 = s then (1 : ℚ) else 0)
          = (if i = k then (if c.getD (k + 1) 0 = s then (1 : ℚ) else 0) else 0) := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        have : i + 2 = c.length := by omega
        simp [this]
      · have hne' : ¬ (i + 2 = c.length ∧ c.getD (i + 1) 0 = s) := by
          rintro ⟨h, -⟩
          exact hik (by omega)
        rw [if_neg hne', if_neg hik]
    rw [sum_congr rfl hres,
      sum_ite_eq' (range (k + 1)) k (fun _ => if c.getD (k + 1) 0 = s then (1 : ℚ) else 0),
      if_pos (mem_range.2 (by omega))]
    conv_rhs => rw [sum_range_succ (fun i => if c.getD i 0 = s then (1 : ℚ) else 0) (k + 1)]

/-- **Divergence of a weighted primitive flow.**  The hypothesis `hsym` says
that the weight takes the same value on the two children of a final block
`m ≥ s + 2`. -/
theorem divOf_wprim (s : ℕ) (hs1 : 1 ≤ s) (φ : List ℕ → ℚ) (c : List ℕ) (hs : Supp c)
    (hne : c ≠ [s])
    (hsym : ∀ i, i + 1 = c.length → s + 2 ≤ c.getD i 0 →
      φ (splitAt c i (c.getD i 0 - s)) = φ (splitAt c i s)) :
    divOf (wprim s φ) c = G c * ∑ i ∈ range c.length,
      ((if s + 2 ≤ c.getD i 0 then tau s (c.getD i 0) * φ (splitAt c i s) else 0)
        - (if c.getD i 0 = s then φ c else 0)) := by
  unfold divOf
  rw [outSumOf_wprim s hs1 φ c hs hsym, inSumOf_wprim s φ c hs hne, mul_assoc, ← mul_sub,
    mul_sum, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [mul_ite, mul_one, mul_zero]

/-! ### Closed forms of `τ_s` for `s = 2, 3, 4` (equation (22)) -/

/-- `τ_3(n) = n(n-2)(n-4)/3`. -/
def tau3 (m : ℕ) : ℚ := (m : ℚ) * ((m : ℚ) - 2) * ((m : ℚ) - 4) / 3

/-- `τ_4(n) = n(n-2)(n-3)(n-5)/8`. -/
def tau4 (m : ℕ) : ℚ := (m : ℚ) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 5) / 8

lemma blockTerm_three : blockTerm 3 = 1 / 3 := by
  norm_num [blockTerm, partQ, factQ, Nat.factorial]

lemma factorial_add_three (n : ℕ) :
    ((n + 3).factorial : ℚ)
      = ((n : ℚ) + 3) * ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n.factorial : ℚ) := by
  rw [Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  ring

lemma factorial_add_four (n : ℕ) :
    ((n + 4).factorial : ℚ)
      = ((n : ℚ) + 4) * ((n : ℚ) + 3) * ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n.factorial : ℚ) := by
  rw [Nat.factorial_succ (n + 3), Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1),
    Nat.factorial_succ n]
  push_cast
  ring

lemma scalar_three (k : ℕ) :
    blockTerm 3 * blockTerm (k + 2) = tau3 (k + 5) * blockTerm (k + 5) := by
  have hf := factorial_add_three (k + 2)
  rw [show k + 2 + 3 = k + 5 from rfl] at hf
  rw [blockTerm_three]
  unfold blockTerm tau3 partQ factQ
  rw [hf]
  have hne : ((k + 2).factorial : ℚ) ≠ 0 := factorial_cast_ne_zero _
  have h3 : ((k : ℚ) + 3) ≠ 0 := by positivity
  have h4 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h5 : ((k : ℚ) + 5) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma scalar_four (k : ℕ) :
    blockTerm 4 * blockTerm (k + 2) = tau4 (k + 6) * blockTerm (k + 6) := by
  have hf := factorial_add_four (k + 2)
  rw [show k + 2 + 4 = k + 6 from rfl] at hf
  rw [blockTerm_four]
  unfold blockTerm tau4 partQ factQ
  rw [hf]
  have hne : ((k + 2).factorial : ℚ) ≠ 0 := factorial_cast_ne_zero _
  have h3 : ((k : ℚ) + 3) ≠ 0 := by positivity
  have h4 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h5 : ((k : ℚ) + 5) ≠ 0 := by positivity
  have h6 : ((k : ℚ) + 6) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `τ_2(n) = n(n-3)/2 = ρ(n)`. -/
theorem tau_two (m : ℕ) (h : 4 ≤ m) : tau 2 m = rho m := by
  unfold tau
  rw [scalar_N m h, mul_div_assoc, div_self (blockTerm_ne_zero m (by omega)), mul_one]

theorem tau_three (m : ℕ) (h : 5 ≤ m) : tau 3 m = tau3 m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
  have e : k + 5 - 3 = k + 2 := by omega
  unfold tau
  rw [e, scalar_three k, mul_div_assoc, div_self (blockTerm_ne_zero _ (by omega)), mul_one]

theorem tau_four (m : ℕ) (h : 6 ≤ m) : tau 4 m = tau4 m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have e : k + 6 - 4 = k + 2 := by omega
  unfold tau
  rw [e, scalar_four k, mul_div_assoc, div_self (blockTerm_ne_zero _ (by omega)), mul_one]

/-- `τ_s(s) = -1` and `τ_s` vanishes at the other support sizes below
`s + 2`: the per-block balance of outflow and inflow, `s = 2`. -/
lemma block_two (m : ℕ) (hm : 2 ≤ m) :
    (if 2 + 2 ≤ m then tau 2 m else 0) - (if m = 2 then 1 else 0) = rho m := by
  by_cases h4 : 4 ≤ m
  · rw [if_pos (by omega), if_neg (by omega), tau_two m h4, sub_zero]
  · have : m = 2 ∨ m = 3 := by omega
    rcases this with rfl | rfl <;> norm_num [rho]

lemma block_three (m : ℕ) (hm : 2 ≤ m) :
    (if 3 + 2 ≤ m then tau 3 m else 0) - (if m = 3 then 1 else 0) = tau3 m := by
  by_cases h5 : 5 ≤ m
  · rw [if_pos (by omega), if_neg (by omega), tau_three m h5, sub_zero]
  · have : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [tau3]

lemma block_four (m : ℕ) (hm : 2 ≤ m) :
    (if 4 + 2 ≤ m then tau 4 m else 0) - (if m = 4 then 1 else 0) = tau4 m := by
  by_cases h6 : 6 ≤ m
  · rw [if_pos (by omega), if_neg (by omega), tau_four m h6, sub_zero]
  · have : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> norm_num [tau4]

/-! ### Lemma 6.1: primitive divergences -/

/-- `T_2(c) = Σ_i τ_2(n_i)`. -/
def T2 (c : List ℕ) : ℚ := (c.map rho).sum
/-- `T_3(c) = Σ_i τ_3(n_i)`. -/
def T3 (c : List ℕ) : ℚ := (c.map tau3).sum
/-- `T_4(c) = Σ_i τ_4(n_i)`. -/
def T4 (c : List ℕ) : ℚ := (c.map tau4).sum

theorem divOf_prim_two (c : List ℕ) (hs : Supp c) (hne : c ≠ [2]) :
    divOf (prim 2) c = G c * T2 c := by
  unfold prim T2
  rw [divOf_wprim 2 (by norm_num) _ c hs hne (fun _ _ _ => rfl), map_sum_eq_range rho c]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  simpa using block_two _ (hs _ (getD_mem c i (mem_range.1 hi)))

theorem divOf_prim_three (c : List ℕ) (hs : Supp c) (hne : c ≠ [3]) :
    divOf (prim 3) c = G c * T3 c := by
  unfold prim T3
  rw [divOf_wprim 3 (by norm_num) _ c hs hne (fun _ _ _ => rfl), map_sum_eq_range tau3 c]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  simpa using block_three _ (hs _ (getD_mem c i (mem_range.1 hi)))

theorem divOf_prim_four (c : List ℕ) (hs : Supp c) (hne : c ≠ [4]) :
    divOf (prim 4) c = G c * T4 c := by
  unfold prim T4
  rw [divOf_wprim 4 (by norm_num) _ c hs hne (fun _ _ _ => rfl), map_sum_eq_range tau4 c]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  simpa using block_four _ (hs _ (getD_mem c i (mem_range.1 hi)))

lemma ne_singleton_of_sum {c : List ℕ} {s : ℕ} (h : s < c.sum) : c ≠ [s] := by
  rintro rfl
  simp at h

/-- **Lemma 6.1 (primitive divergences).**  For `d ≥ 3`, that is for
compositions of `N ≥ 5`, `div F_s = G · T_s` for `s = 2, 3, 4`. -/
theorem primitive_divergences (c : List ℕ) (hs : Supp c) (h5 : 5 ≤ c.sum) :
    divOf (prim 2) c = G c * T2 c ∧ divOf (prim 3) c = G c * T3 c ∧
      divOf (prim 4) c = G c * T4 c :=
  ⟨divOf_prim_two c hs (ne_singleton_of_sum (by omega)),
    divOf_prim_three c hs (ne_singleton_of_sum (by omega)),
    divOf_prim_four c hs (ne_singleton_of_sum (by omega))⟩

/-! ### Lemma 6.2: the discrete product rule -/

/-- `v(n) = n(n-2)`. -/
def vq (n : ℕ) : ℚ := (n : ℚ) * ((n : ℚ) - 2)

/-- `V(c) = Σ_i n_i(n_i-2)`. -/
def V (c : List ℕ) : ℚ := (c.map vq).sum

/-- `Q_2(c) = Σ_i v_i^2`. -/
def Q2 (c : List ℕ) : ℚ := (c.map fun n => vq n ^ 2).sum

/-- `F_{2,V}`: the selected occurrences of `F_2`, with raw flow
`G(child) V(child)`. -/
def F2V : EdgeFlow := wprim 2 V

lemma V_append (l₁ l₂ : List ℕ) : V (l₁ ++ l₂) = V l₁ + V l₂ := by
  simp [V, List.sum_append]

lemma V_cons (a : ℕ) (l : List ℕ) : V (a :: l) = vq a + V l := by
  simp [V]

/-- The effect of a split on `V`. -/
lemma V_splitAt (c : List ℕ) (i p : ℕ) (hi : i < c.length) :
    V (splitAt c i p) = V c - vq (c.getD i 0) + vq p + vq (c.getD i 0 - p) := by
  have hd := decomp_at c i hi
  have h1 : V c = V (c.take i) + (vq (c.getD i 0) + V (c.drop (i + 1))) := by
    conv_lhs => rw [hd]
    rw [V_append, V_cons]
  rw [splitAt_eq, V_append, V_cons, V_cons, h1]
  ring

/-- `T_2 = (V - N)/2`. -/
lemma T2_eq (c : List ℕ) : T2 c = (V c - (c.sum : ℚ)) / 2 := by
  induction c with
  | nil => simp [T2, V]
  | cons a l ih =>
    have h1 : T2 (a :: l) = rho a + T2 l := by simp [T2]
    have h3 : ((a :: l).sum : ℚ) = (a : ℚ) + (l.sum : ℚ) := by simp
    rw [h1, V_cons, h3, ih]
    unfold rho vq
    ring

/-- Equation (26): `Q_2 - 9V = 8 T_4 + 18 T_3`, from the one-variable
identity (25). -/
lemma Q2_sub_nine_V (c : List ℕ) : Q2 c - 9 * V c = 8 * T4 c + 18 * T3 c := by
  induction c with
  | nil => simp [Q2, V, T4, T3]
  | cons a l ih =>
    have h1 : Q2 (a :: l) = vq a ^ 2 + Q2 l := by simp [Q2]
    have h2 : T4 (a :: l) = tau4 a + T4 l := by simp [T4]
    have h3 : T3 (a :: l) = tau3 a + T3 l := by simp [T3]
    have key : vq a ^ 2 - 9 * vq a = 8 * tau4 a + 18 * tau3 a := by
      unfold vq tau4 tau3
      ring
    rw [h1, h2, h3, V_cons]
    linear_combination ih + key

/-- **Lemma 6.2 (discrete product rule).**
`div F_{2,V} / G = V(V-N)/2 - 6 T_3 - 2V`. -/
theorem divOf_F2V (c : List ℕ) (hs : Supp c) (hne : c ≠ [2]) :
    divOf F2V c = G c * (V c * (V c - (c.sum : ℚ)) / 2 - 6 * T3 c - 2 * V c) := by
  have hsym : ∀ i, i + 1 = c.length → 2 + 2 ≤ c.getD i 0 →
      V (splitAt c i (c.getD i 0 - 2)) = V (splitAt c i 2) := by
    intro i hi _
    have hlt : i < c.length := by omega
    have hm := hs _ (getD_mem c i hlt)
    rw [V_splitAt c i _ hlt, V_splitAt c i 2 hlt,
      show c.getD i 0 - (c.getD i 0 - 2) = 2 by omega]
    ring
  have hblock : ∀ i ∈ range c.length,
      ((if 2 + 2 ≤ c.getD i 0 then tau 2 (c.getD i 0) * V (splitAt c i 2) else 0)
        - (if c.getD i 0 = 2 then V c else 0))
      = V c * rho (c.getD i 0) - 6 * tau3 (c.getD i 0) - 2 * vq (c.getD i 0) := by
    intro i hi
    have hlt := mem_range.1 hi
    have hm := hs _ (getD_mem c i hlt)
    by_cases h4 : 4 ≤ c.getD i 0
    · rw [if_pos (by omega), if_neg (by omega), tau_two _ h4, V_splitAt c i 2 hlt]
      have hc : ((c.getD i 0 - 2 : ℕ) : ℚ) = (c.getD i 0 : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      unfold vq rho tau3
      rw [hc]
      push_cast
      ring
    · have : c.getD i 0 = 2 ∨ c.getD i 0 = 3 := by omega
      rcases this with h | h <;> rw [h] <;> norm_num [tau3, vq, rho]
  unfold F2V
  rw [divOf_wprim 2 (by norm_num) V c hs hne hsym, sum_congr rfl hblock, sum_sub_distrib,
    sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← map_sum_eq_range rho c,
    ← map_sum_eq_range tau3 c, ← map_sum_eq_range vq c]
  have hT : (c.map rho).sum = (V c - (c.sum : ℚ)) / 2 := T2_eq c
  rw [hT]
  unfold T3 V
  ring

/-! ### Proposition 6.3: the signed flow -/

/-- The signed flow (27):
`f_0 = 30 F_{2,V} + (30N - 12) F_2 + 72 F_3 - 48 F_4`, with `N` the sum of
the parent composition. -/
def f0 : EdgeFlow := fun c i p =>
  30 * F2V c i p + (30 * (c.sum : ℚ) - 12) * prim 2 c i p + 72 * prim 3 c i p
    - 48 * prim 4 c i p

/-- The same flow occurrence by occurrence: an `F_2` occurrence has
coefficient `30 V(child) + 30N - 12`, an `F_3` occurrence `72`, an `F_4`
occurrence `-48`, each multiplying `G(child)`. -/
theorem f0_eq (c : List ℕ) (i p : ℕ) :
    f0 c i p =
      (ind 2 c i p * (30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12)
        + ind 3 c i p * 72 - ind 4 c i p * 48) * G (splitAt c i p) := by
  unfold f0 F2V prim wprim
  ring

/-- `S_4(c) = 15 V^2 - 6 Q_2 - 12 V - B_d` with `B_d = 15N^2 - 6N`, the
value for `d ≥ 3` (equations (18) and (21)). -/
def S4 (c : List ℕ) : ℚ :=
  15 * V c ^ 2 - 6 * Q2 c - 12 * V c - (15 * (c.sum : ℚ) ^ 2 - 6 * (c.sum : ℚ))

/-- The target `w^{(4)} = G S_4` (equation (21)), for `d ≥ 3`. -/
def w4 (c : List ℕ) : ℚ := G c * S4 c

/-- The coefficient `a^{(4)} = Π(n_i - 1) · S_4` (equation (20)), for `d ≥ 3`. -/
def a4 (c : List ℕ) : ℚ := (c.map partQ).prod * S4 c

/-- `w^{(4)} = U · a^{(4)}` with `U` the Boolean flag number of the `k = 2`
files. -/
theorem w4_eq_U_mul_a4 (c : List ℕ) : w4 c = U c * a4 c := by
  unfold w4 U a4 G
  rw [gprod_eq_div]
  have h := factprod_ne_zero c
  field_simp

/-- `B_d = 3(d+2)(5d+8) = 15N^2 - 6N` for `N = d + 2`. -/
theorem Bd_eq (d : ℕ) :
    15 * ((d + 2 : ℕ) : ℚ) ^ 2 - 6 * ((d + 2 : ℕ) : ℚ) = 3 * ((d : ℚ) + 2) * (5 * (d : ℚ) + 8) := by
  push_cast
  ring

lemma outSumOf_f0 (c : List ℕ) :
    outSumOf f0 c = 30 * outSumOf F2V c + (30 * (c.sum : ℚ) - 12) * outSumOf (prim 2) c
      + 72 * outSumOf (prim 3) c - 48 * outSumOf (prim 4) c := by
  simp only [outSumOf, f0, sum_add_distrib, sum_sub_distrib, mul_sum]

lemma inSumOf_f0 (c : List ℕ) :
    inSumOf f0 c = 30 * inSumOf F2V c + (30 * (c.sum : ℚ) - 12) * inSumOf (prim 2) c
      + 72 * inSumOf (prim 3) c - 48 * inSumOf (prim 4) c := by
  have h : ∀ i ∈ range (c.length - 1), f0 (mergeAt c i) i (c.getD i 0)
      = 30 * F2V (mergeAt c i) i (c.getD i 0)
        + (30 * (c.sum : ℚ) - 12) * prim 2 (mergeAt c i) i (c.getD i 0)
        + 72 * prim 3 (mergeAt c i) i (c.getD i 0)
        - 48 * prim 4 (mergeAt c i) i (c.getD i 0) := by
    intro i hi
    have hlt : i + 1 < c.length := by
      have := mem_range.1 hi
      omega
    simp only [f0, mergeAt_sum c i hlt]
  simp only [inSumOf]
  rw [sum_congr rfl h]
  simp only [sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Linearity of the divergence for the combination (27). -/
theorem divOf_f0_eq (c : List ℕ) :
    divOf f0 c = 30 * divOf F2V c + (30 * (c.sum : ℚ) - 12) * divOf (prim 2) c
      + 72 * divOf (prim 3) c - 48 * divOf (prim 4) c := by
  unfold divOf
  rw [outSumOf_f0, inSumOf_f0]
  ring

/-- **Proposition 6.3 (signed fourth-moment flow).**  At every support
composition of `N ≥ 5`, that is for `d ≥ 3` and `N = d + 2`,
`div f_0 = w^{(4)}`. -/
theorem divOf_f0 (c : List ℕ) (hs : Supp c) (h5 : 5 ≤ c.sum) : divOf f0 c = w4 c := by
  obtain ⟨h2, h3, h4⟩ := primitive_divergences c hs h5
  rw [divOf_f0_eq, divOf_F2V c hs (ne_singleton_of_sum (by omega)), h2, h3, h4]
  have hT2 := T2_eq c
  have hQ := Q2_sub_nine_V c
  unfold w4 S4
  linear_combination (G c * (30 * (c.sum : ℚ) - 12)) * hT2 + (6 * G c) * hQ

/-! ### Diagnostic values

`N = 5` (`d = 3`), `c = (5)`: the two edges `(5) → (2,3)` and
`(5) → (3,2)` carry `3600` and `2400`, there is no inflow, and
`w^{(4)}(5) = 6000`.  The values are computed from the definitions, not
from the theorem. -/

example : f0 [5] 0 2 = 3600 := by
  norm_num [f0, F2V, prim, wprim, ind, indNs, indFLs, indFRs, Supp, splitAt, G, V, vq, gprod,
    blockTerm, partQ, factQ, lastPart, Nat.factorial]

example : f0 [5] 0 3 = 2400 := by
  norm_num [f0, F2V, prim, wprim, ind, indNs, indFLs, indFRs, Supp, splitAt, G, V, vq, gprod,
    blockTerm, partQ, factQ, lastPart, Nat.factorial]

example : w4 [5] = 6000 := by
  norm_num [w4, S4, G, V, Q2, vq, gprod, blockTerm, partQ, factQ, lastPart, Nat.factorial]

/-! The balanced edge `(8) → (4,4)` carries two `F_4` occurrences. -/

example : ind 4 [8] 0 4 = 2 := by
  norm_num [ind, indNs, indFLs, indFRs, Supp]

end K4
end ChowCone
