/-
Outflow (Draft Corollary 6), inflow (Draft Lemma 7) and the divergence
identity `div f = w` (Draft Theorem 1, §7).
-/
import ChowCone.Ratios

namespace ChowCone

open Finset

/-! ### More list helpers -/

lemma getD_mem (c : List ℕ) (i : ℕ) (hi : i < c.length) : c.getD i 0 ∈ c := by
  rw [List.getD_eq_getElem c 0 hi]
  exact List.getElem_mem hi

lemma take_append_length (l₁ l₂ : List ℕ) : (l₁ ++ l₂).take l₁.length = l₁ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    rw [List.cons_append, List.length_cons, List.take_succ_cons, ih]

lemma drop_append_length_succ (l₁ l₂ : List ℕ) (x : ℕ) :
    (l₁ ++ x :: l₂).drop (l₁.length + 1) = l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    rw [List.cons_append, List.length_cons]
    rw [show l.length + 1 + 1 = (l.length + 1) + 1 from rfl,
        List.drop_succ_cons]
    exact ih

lemma map_sum_eq_range (f : ℕ → ℚ) (c : List ℕ) :
    (c.map f).sum = ∑ i ∈ Finset.range c.length, f (c.getD i 0) := by
  induction c with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons,
        Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-! ### Outflow (Draft Corollary 6) -/

lemma F_eq_zero_of_small (c : List ℕ) (i p : ℕ) (h : ¬ 4 ≤ c.getD i 0) :
    F c i p = 0 := by
  unfold F indN indFL indFR
  rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
  ring

/-- Nonfinal block: only the (N)-move fires (Draft Def. 4 + Lemma 5). -/
lemma F_formula_nonfinal (c : List ℕ) (i p : ℕ) (hs : Supp c)
    (hi : i + 1 < c.length) (h4 : 4 ≤ c.getD i 0) :
    F c i p = if p = 2 then rho (c.getD i 0) * G c else 0 := by
  have hFL : indFL c i p = 0 := by
    unfold indFL
    rw [if_neg]
    rintro ⟨-, h, -, -⟩
    omega
  have hFR : indFR c i p = 0 := by
    unfold indFR
    rw [if_neg]
    rintro ⟨-, h, -, -⟩
    omega
  unfold F
  rw [hFL, hFR]
  by_cases hp : p = 2
  · subst hp
    have hN : indN c i 2 = 1 := by
      unfold indN
      exact if_pos ⟨hs, hi, rfl, h4⟩
    rw [hN, if_pos rfl, G_splitAt_nonfinal c i hi h4]
    ring
  · have hN : indN c i p = 0 := by
      unfold indN
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hp h
    rw [hN, if_neg hp]
    ring

/-- Final block: the (FL)- and (FR)-moves fire (Draft Def. 4 + Lemma 5);
for a final block 4 both land on the same offset and add up. -/
lemma F_formula_final (c : List ℕ) (i p : ℕ) (hs : Supp c)
    (hi : i + 1 = c.length) (h4 : 4 ≤ c.getD i 0) :
    F c i p
      = (if p = 2 then
          (((c.getD i 0 : ℚ) - 2) * ((c.getD i 0 : ℚ) - 3) / 2) * G c else 0)
      + (if p = c.getD i 0 - 2 then ((c.getD i 0 : ℚ) - 3) * G c else 0) := by
  have hN : indN c i p = 0 := by
    unfold indN
    rw [if_neg]
    rintro ⟨-, h, -, -⟩
    omega
  have hL := G_splitAt_final_left c i hi h4
  have hR := G_splitAt_final_right c i hi h4
  unfold F
  rw [hN]
  by_cases hp2 : p = 2 <;> by_cases hpr : p = c.getD i 0 - 2
  · -- both fire: final block 4, coincident edge, flow 2·G(child)
    subst hp2
    have hFL : indFL c i 2 = 1 := by
      unfold indFL
      exact if_pos ⟨hs, hi, rfl, h4⟩
    have hFR : indFR c i 2 = 1 := by
      unfold indFR
      exact if_pos ⟨hs, hi, hpr, h4⟩
    rw [hFL, hFR, if_pos rfl, if_pos hpr]
    rw [← hpr] at hR
    rw [hL] at hR ⊢
    linarith
  · subst hp2
    have hFL : indFL c i 2 = 1 := by
      unfold indFL
      exact if_pos ⟨hs, hi, rfl, h4⟩
    have hFR : indFR c i 2 = 0 := by
      unfold indFR
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hpr h
    rw [hFL, hFR, if_pos rfl, if_neg hpr, hL]
    ring
  · subst hpr
    have hFL : indFL c i (c.getD i 0 - 2) = 0 := by
      unfold indFL
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hp2 h
    have hFR : indFR c i (c.getD i 0 - 2) = 1 := by
      unfold indFR
      exact if_pos ⟨hs, hi, rfl, h4⟩
    rw [hFL, hFR, if_neg hp2, if_pos rfl, hR]
    ring
  · have hFL : indFL c i p = 0 := by
      unfold indFL
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hp2 h
    have hFR : indFR c i p = 0 := by
      unfold indFR
      rw [if_neg]
      rintro ⟨-, -, h, -⟩
      exact hpr h
    rw [hFL, hFR, if_neg hp2, if_neg hpr]
    ring

/-- Per-block outflow: `Σ_p F(c,i,p) = G(c)·ρ⁺(c_i)` (Draft Corollary 6). -/
lemma sum_p_F (c : List ℕ) (i : ℕ) (hs : Supp c) (hi : i < c.length) :
    ∑ p ∈ Finset.Icc 1 (c.getD i 0 - 1), F c i p
      = G c * (if 4 ≤ c.getD i 0 then rho (c.getD i 0) else 0) := by
  by_cases h4 : 4 ≤ c.getD i 0
  · rw [if_pos h4]
    have hmem2 : 2 ∈ Finset.Icc 1 (c.getD i 0 - 1) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hmemr : c.getD i 0 - 2 ∈ Finset.Icc 1 (c.getD i 0 - 1) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt | heq
    · rw [Finset.sum_congr rfl
        (fun p _ => F_formula_nonfinal c i p hs hlt h4)]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 (c.getD i 0 - 1)) 2
        (fun _ => rho (c.getD i 0) * G c)]
      rw [if_pos hmem2]
      ring
    · rw [Finset.sum_congr rfl
        (fun p _ => F_formula_final c i p hs heq h4)]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 (c.getD i 0 - 1)) 2
        (fun _ => (((c.getD i 0 : ℚ) - 2) * ((c.getD i 0 : ℚ) - 3) / 2) * G c)]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 (c.getD i 0 - 1)) (c.getD i 0 - 2)
        (fun _ => ((c.getD i 0 : ℚ) - 3) * G c)]
      rw [if_pos hmem2, if_pos hmemr]
      unfold rho
      ring
  · rw [if_neg h4]
    rw [Finset.sum_congr rfl fun p _ => F_eq_zero_of_small c i p h4]
    simp

/-- Total outflow (Draft Corollary 6). -/
lemma outSum_eq (c : List ℕ) (hs : Supp c) :
    outSum c = G c * ∑ i ∈ Finset.range c.length,
      (if 4 ≤ c.getD i 0 then rho (c.getD i 0) else 0) := by
  unfold outSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi =>
    sum_p_F c i hs (Finset.mem_range.1 hi)

/-! ### Inflow (Draft Lemma 7) -/

lemma mergeAt_def (c : List ℕ) (i : ℕ) :
    mergeAt c i
      = c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2) := rfl

/-- Reversing a merge by the recorded split recovers `c` (Draft Lemma 7,
completeness of the reverse map). -/
lemma splitAt_mergeAt (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    splitAt (mergeAt c i) i (c.getD i 0) = c := by
  have hle : i ≤ c.length := by omega
  have hlen : (c.take i).length = i := length_take_of_lt c i hle
  have h1 : (c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2)).take
      ((c.take i).length) = c.take i := take_append_length _ _
  have h2 : (c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2)).getD
      ((c.take i).length) 0 = c.getD i 0 + c.getD (i + 1) 0 :=
    getD_append_length _ _ _
  have h3 : (c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2)).drop
      ((c.take i).length + 1) = c.drop (i + 2) := drop_append_length_succ _ _ _
  rw [hlen] at h1 h2 h3
  rw [splitAt_eq, mergeAt_def, h1, h2, h3]
  rw [show c.getD i 0 + c.getD (i + 1) 0 - c.getD i 0 = c.getD (i + 1) 0
    by omega]
  exact (decomp_at2 c i hi).symm

lemma mergeAt_getD (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    (mergeAt c i).getD i 0 = c.getD i 0 + c.getD (i + 1) 0 := by
  have hle : i ≤ c.length := by omega
  have hlen : (c.take i).length = i := length_take_of_lt c i hle
  have h2 : (c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2)).getD
      ((c.take i).length) 0 = c.getD i 0 + c.getD (i + 1) 0 :=
    getD_append_length _ _ _
  rw [hlen] at h2
  rw [mergeAt_def]
  exact h2

lemma mergeAt_length (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    (mergeAt c i).length = c.length - 1 := by
  have hle : i ≤ c.length := by omega
  rw [mergeAt_def, List.length_append, List.length_cons,
      length_take_of_lt c i hle, List.length_drop]
  omega

lemma Supp_mergeAt (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length)
    (hs : Supp c) : Supp (mergeAt c i) := by
  intro x hx
  rw [mergeAt_def] at hx
  rcases List.mem_append.1 hx with h | h
  · exact hs x (List.take_subset i c h)
  · rcases List.mem_cons.1 h with h | h
    · subst h
      have h1 := hs _ (getD_mem c i (by omega))
      omega
    · exact hs x (List.drop_subset (i + 2) c h)

/-- The in-flow formula (Draft Lemma 7, per adjacent pair). -/
lemma F_merge (c : List ℕ) (i : ℕ) (hs : Supp c) (hi : i + 1 < c.length) :
    F (mergeAt c i) i (c.getD i 0)
      = G c * ((if c.getD i 0 = 2 then 1 else 0)
             + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = 2 then 1 else 0)) := by
  have hq : Supp (mergeAt c i) := Supp_mergeAt c i hi hs
  have hlen : (mergeAt c i).length = c.length - 1 := mergeAt_length c i hi
  have hget : (mergeAt c i).getD i 0 = c.getD i 0 + c.getD (i + 1) 0 :=
    mergeAt_getD c i hi
  have hsplit := splitAt_mergeAt c i hi
  have hb := hs _ (getD_mem c (i + 1) hi)
  have ha := hs _ (getD_mem c i (by omega))
  have e1 : (i + 1 < (mergeAt c i).length) ↔ (i + 2 < c.length) := by
    rw [hlen]; omega
  have e2 : (i + 1 = (mergeAt c i).length) ↔ (i + 2 = c.length) := by
    rw [hlen]; omega
  have e3 : (c.getD i 0 = c.getD i 0 + c.getD (i + 1) 0 - 2)
      ↔ (c.getD (i + 1) 0 = 2) := by omega
  have h4' : 4 ≤ c.getD i 0 + c.getD (i + 1) 0 := by omega
  unfold F
  rw [hsplit]
  unfold indN indFL indFR
  rw [hget]
  have key :
      ((if Supp (mergeAt c i) ∧ i + 1 < (mergeAt c i).length ∧
            c.getD i 0 = 2 ∧ 4 ≤ c.getD i 0 + c.getD (i + 1) 0
          then (1 : ℚ) else 0)
        + (if Supp (mergeAt c i) ∧ i + 1 = (mergeAt c i).length ∧
            c.getD i 0 = 2 ∧ 4 ≤ c.getD i 0 + c.getD (i + 1) 0
          then (1 : ℚ) else 0)
        + (if Supp (mergeAt c i) ∧ i + 1 = (mergeAt c i).length ∧
            c.getD i 0 = c.getD i 0 + c.getD (i + 1) 0 - 2 ∧
            4 ≤ c.getD i 0 + c.getD (i + 1) 0
          then (1 : ℚ) else 0))
      = (if c.getD i 0 = 2 then 1 else 0)
        + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = 2 then 1 else 0) := by
    simp only [hq, h4', true_and, and_true, e1, e2, e3]
    rcases Nat.lt_or_ge (i + 2) c.length with hlt | hge
    · have hne : ¬ (i + 2 = c.length) := by omega
      simp [hlt, hne]
    · have heq : i + 2 = c.length := by omega
      have hnlt : ¬ (i + 2 < c.length) := by omega
      simp [heq, hnlt]
  rw [key]
  ring

/-! ### Inflow total (Draft Lemma 7) -/

lemma inSum_eq (c : List ℕ) (hs : Supp c) (hsum : 3 ≤ c.sum) :
    inSum c
      = G c * ∑ i ∈ Finset.range c.length,
          (if c.getD i 0 = 2 then 1 else 0) := by
  unfold inSum
  rcases hlen : c.length with _ | n
  · exfalso
    have : c = [] := List.length_eq_zero_iff.1 hlen
    subst this
    simp at hsum
  rcases n with _ | k
  · -- single block: sum ≥ 3 forces the block ≥ 3, so no 2-blocks, no edges
    have hc : c = [c.getD 0 0] := by
      have h0 : (0 : ℕ) < c.length := by omega
      have hd := decomp_at c 0 h0
      have hdrop : c.drop 1 = [] := by
        apply List.drop_eq_nil_iff.2
        omega
      rw [hdrop] at hd
      simpa using hd
    have hge : 3 ≤ c.getD 0 0 := by
      have : c.sum = c.getD 0 0 := by
        conv_lhs => rw [hc]
        simp
      omega
    rw [show (1 : ℕ) - 1 = 0 from rfl, Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [if_neg (by omega)]
    ring
  · -- length = k + 2 ≥ 2
    have hstep : ∀ i ∈ Finset.range (k + 1),
        F (mergeAt c i) i (c.getD i 0)
          = G c * ((if c.getD i 0 = 2 then 1 else 0)
                 + (if i + 2 = c.length ∧ c.getD (i + 1) 0 = 2
                    then 1 else 0)) := by
      intro i hi
      exact F_merge c i hs (by
        have := Finset.mem_range.1 hi
        omega)
    rw [show k + 1 + 1 - 1 = k + 1 from rfl]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib]
    have hres : ∀ i ∈ Finset.range (k + 1),
        (if i + 2 = c.length ∧ c.getD (i + 1) 0 = 2 then (1 : ℚ) else 0)
          = (if i = k then (if c.getD (k + 1) 0 = 2 then (1 : ℚ) else 0)
             else 0) := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        have : i + 2 = c.length ↔ True := by
          constructor
          · intro; trivial
          · intro; omega
        simp [this]
      · have hne : ¬ (i + 2 = c.length ∧ c.getD (i + 1) 0 = 2) := by
          rintro ⟨h, -⟩
          exact hik (by omega)
        rw [if_neg hne, if_neg hik]
    rw [Finset.sum_congr rfl hres]
    rw [Finset.sum_ite_eq' (Finset.range (k + 1)) k
      (fun _ => if c.getD (k + 1) 0 = 2 then (1 : ℚ) else 0)]
    rw [if_pos (Finset.mem_range.2 (by omega))]
    conv_rhs => rw [Finset.sum_range_succ
      (fun i => if c.getD i 0 = 2 then (1 : ℚ) else 0) (k + 1)]

/-! ### The divergence identity (Draft Theorem 1, §7) -/

/-- Main combinatorial theorem: `div f = w` at every support composition
with total sum ≥ 3 (i.e. every `d ≥ 1`). -/
theorem flowDiv_eq_w (c : List ℕ) (hs : Supp c) (hsum : 3 ≤ c.sum) :
    flowDiv c = w c := by
  unfold flowDiv w
  rw [outSum_eq c hs, inSum_eq c hs hsum, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib, map_sum_eq_range rho c]
  apply Finset.sum_congr rfl
  intro i hi
  have hm : 2 ≤ c.getD i 0 := hs _ (getD_mem c i (Finset.mem_range.1 hi))
  by_cases h4 : 4 ≤ c.getD i 0
  · rw [if_pos h4, if_neg (by omega)]
    ring
  · have : c.getD i 0 = 2 ∨ c.getD i 0 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num

/-- Non-support nodes have no incident selected in-edges (Draft §7). -/
lemma F_merge_eq_zero_of_not_supp (c : List ℕ) (i : ℕ)
    (hi : i + 1 < c.length) (hns : ¬ Supp c) :
    F (mergeAt c i) i (c.getD i 0) = 0 := by
  by_cases hc : Supp (mergeAt c i) ∧ 2 ≤ c.getD i 0 ∧
      2 ≤ (mergeAt c i).getD i 0 - c.getD i 0
  · exfalso
    apply hns
    have := Supp_splitAt (mergeAt c i) i (c.getD i 0) hc.1 hc.2.1 hc.2.2
    rwa [splitAt_mergeAt c i hi] at this
  · unfold F
    rw [indN_eq_zero _ _ _ hc, indFL_eq_zero _ _ _ hc, indFR_eq_zero _ _ _ hc]
    ring

/-- The divergence identity over ALL composition nodes with parts ≥ 1
(the whole Boolean lattice, Draft §7): `div f = w`. -/
theorem flowDiv_eq_w_all (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m)
    (hsum : 3 ≤ c.sum) : flowDiv c = w c := by
  by_cases hs : Supp c
  · exact flowDiv_eq_w c hs hsum
  · have hone : 1 ∈ c := by
      unfold Supp at hs
      push_neg at hs
      obtain ⟨m, hm, hlt⟩ := hs
      have h1m := h1 m hm
      have : m = 1 := by omega
      rwa [this] at hm
    rw [w_eq_zero_of_one_mem c hone]
    unfold flowDiv
    have hout : outSum c = 0 := by
      unfold outSum
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro p _
      exact F_eq_zero_of_not_supp c i p hs
    have hin : inSum c = 0 := by
      unfold inSum
      apply Finset.sum_eq_zero
      intro i hi
      exact F_merge_eq_zero_of_not_supp c i
        (by have := Finset.mem_range.1 hi; omega) hs
    rw [hout, hin]
    ring

end ChowCone
