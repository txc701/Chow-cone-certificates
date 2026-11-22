/-
Collision accounting and nonnegativity of `f_d` (Proposition 8.2).

Manuscript of 21 November 2026: Section 7, the amounts (30) of the charges
of the left square and the amount `24(t+2)(t-1)` of the final-right square;
Section 8, the reserve (35) of an `F_2` occurrence, Table 1, and
Proposition 8.2 with its three margin polynomials.

Scope.  This file proves that every edge value of `f_d` is nonnegative on
the compositions of `N`.  It uses the origins of the charges
(`CascadeOrigins`, `SquareCharges`), the bounds `75` and `60` on the cascade
totals (`CascadeSizes`) and the evaluation of `f_d` (`Evaluation`).  It does
not treat `d = 1, 2`, and it does not prove Theorem 9.1.
-/
import ChowCone.K4.Evaluation

namespace ChowCone
namespace K4

open Finset

/-! ### The amounts of the charges of rows 1–3 (equation (30)) -/

lemma lastPart_append_cons_cons (l : List ℕ) (a b : ℕ) (S : List ℕ) :
    lastPart (l ++ a :: b :: S) = lastPart (b :: S) :=
  lastPart_append_cons_of_ne l (b :: S) a (by simp)

/-- Row 2: `48 G(B) = 24 G(D)` for `B = P.(4,t).S`, `D = P.(2,2,t).S`. -/
theorem amount_CD (P S : List ℕ) (t : ℕ) :
    48 * G (P ++ 4 :: t :: S) = 24 * G (P ++ 2 :: 2 :: t :: S) := by
  unfold G
  have hsum : (P ++ 4 :: t :: S).sum = (P ++ 2 :: 2 :: t :: S).sum := by
    simp only [List.sum_append, List.sum_cons]
    omega
  have hl1 : lastPart (P ++ 4 :: t :: S) = lastPart (t :: S) := lastPart_append_cons_cons _ _ _ _
  have hl2 : lastPart (P ++ 2 :: 2 :: t :: S) = lastPart (t :: S) := by
    rw [show P ++ 2 :: 2 :: t :: S = (P ++ [2]) ++ 2 :: t :: S by simp,
      lastPart_append_cons_cons]
  rw [hsum, hl1, hl2]
  simp only [gprod_append, gprod_cons, blockTerm_two, blockTerm_four]
  ring

/-- Row 1, nonfinal block: `48 G(B) = 12(t+2)(t-1) G(C)` for
`B = P.(4,t).S`, `C = P.(2,t+2).S`, `S` nonempty. -/
theorem amount_AC_nonfinal (P S : List ℕ) (t : ℕ) (ht : 2 ≤ t) (hS : S ≠ []) :
    48 * G (P ++ 4 :: t :: S)
      = 12 * ((t : ℚ) + 2) * ((t : ℚ) - 1) * G (P ++ 2 :: (t + 2) :: S) := by
  unfold G
  have hsum : (P ++ 4 :: t :: S).sum = (P ++ 2 :: (t + 2) :: S).sum := by
    simp only [List.sum_append, List.sum_cons]
    omega
  have hl1 : lastPart (P ++ 4 :: t :: S) = lastPart S := by
    rw [lastPart_append_cons_cons, lastPart_cons_of_ne t S hS]
  have hl2 : lastPart (P ++ 2 :: (t + 2) :: S) = lastPart S := by
    rw [lastPart_append_cons_cons, lastPart_cons_of_ne (t + 2) S hS]
  rw [hsum, hl1, hl2]
  simp only [gprod_append, gprod_cons, blockTerm_two, blockTerm_four, blockTerm_add_two t ht]
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℚ) + 2 ≠ 0 := by positivity
  have h2 : (t : ℚ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Row 1, final block: `48 G(B) = 12 t(t-1) G(C)` for `B = P.(4,t)`,
`C = P.(2,t+2)`. -/
theorem amount_AC_final (P : List ℕ) (t : ℕ) (ht : 2 ≤ t) :
    48 * G (P ++ [4, t]) = 12 * (t : ℚ) * ((t : ℚ) - 1) * G (P ++ [2, t + 2]) := by
  unfold G
  have hsum : (P ++ [4, t]).sum = (P ++ [2, t + 2]).sum := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    omega
  rw [hsum, lastPart_append_pair, lastPart_append_pair]
  simp only [gprod_append, gprod_cons, gprod_nil, blockTerm_two, blockTerm_four,
    blockTerm_add_two t ht]
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℚ) + 2 ≠ 0 := by positivity
  have h2 : (t : ℚ) - 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-- Row 3: `48 G(B) = 24(t+2)(t-1) G(C)` for `B = P.(t,4)`,
`C = P.(t+2,2)`. -/
theorem amount_right_AC (P : List ℕ) (t : ℕ) (ht : 2 ≤ t) :
    48 * G (P ++ [t, 4]) = 24 * ((t : ℚ) + 2) * ((t : ℚ) - 1) * G (P ++ [t + 2, 2]) := by
  unfold G
  have hsum : (P ++ [t, 4]).sum = (P ++ [t + 2, 2]).sum := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    omega
  rw [hsum, lastPart_append_pair, lastPart_append_pair]
  simp only [gprod_append, gprod_cons, gprod_nil, blockTerm_two, blockTerm_four,
    blockTerm_add_two t ht]
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℚ) + 2 ≠ 0 := by positivity
  have h2 : (t : ℚ) - 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-! ### Facts about the indicators -/

lemma indNs_cases (s : ℕ) (c : List ℕ) (i p : ℕ) : indNs s c i p = 0 ∨ indNs s c i p = 1 := by
  unfold indNs
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma indFLs_cases (s : ℕ) (c : List ℕ) (i p : ℕ) :
    indFLs s c i p = 0 ∨ indFLs s c i p = 1 := by
  unfold indFLs
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma indFRs_cases (s : ℕ) (c : List ℕ) (i p : ℕ) :
    indFRs s c i p = 0 ∨ indFRs s c i p = 1 := by
  unfold indFRs
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma indNs_eq_one {s : ℕ} {c : List ℕ} {i p : ℕ} (h : indNs s c i p = 1) :
    Supp c ∧ i + 1 < c.length ∧ p = s ∧ s + 2 ≤ c.getD i 0 := by
  unfold indNs at h
  exact (ite_one_zero_eq_one_iff _).1 h

lemma indFLs_eq_one {s : ℕ} {c : List ℕ} {i p : ℕ} (h : indFLs s c i p = 1) :
    Supp c ∧ i + 1 = c.length ∧ p = s ∧ s + 2 ≤ c.getD i 0 := by
  unfold indFLs at h
  exact (ite_one_zero_eq_one_iff _).1 h

lemma indFRs_eq_one {s : ℕ} {c : List ℕ} {i p : ℕ} (h : indFRs s c i p = 1) :
    Supp c ∧ i + 1 = c.length ∧ p = c.getD i 0 - s ∧ s + 2 ≤ c.getD i 0 := by
  unfold indFRs at h
  exact (ite_one_zero_eq_one_iff _).1 h

/-- A nonfinal block `m ≥ s + 2` after the prefix `P`. -/
lemma indNs_append (s : ℕ) (P S : List ℕ) (m : ℕ) (hsupp : Supp (P ++ m :: S)) (hS : S ≠ [])
    (hm : s + 2 ≤ m) : indNs s (P ++ m :: S) P.length s = 1 := by
  unfold indNs
  rw [if_pos]
  refine ⟨hsupp, ?_, rfl, ?_⟩
  · have : 0 < S.length := List.length_pos_iff.2 hS
    simp only [List.length_append, List.length_cons]
    omega
  · rw [getD_append_length]
    exact hm

lemma indFLs_append_of_ne (s : ℕ) (P S : List ℕ) (m p : ℕ) (hS : S ≠ []) :
    indFLs s (P ++ m :: S) P.length p = 0 := by
  unfold indFLs
  rw [if_neg]
  rintro ⟨-, h, -, -⟩
  have : 0 < S.length := List.length_pos_iff.2 hS
  simp only [List.length_append, List.length_cons] at h
  omega

/-- A final block `m ≥ s + 2` after the prefix `P`, left orientation. -/
lemma indFLs_append (s : ℕ) (P : List ℕ) (m : ℕ) (hsupp : Supp (P ++ [m])) (hm : s + 2 ≤ m) :
    indFLs s (P ++ [m]) P.length s = 1 := by
  unfold indFLs
  rw [if_pos]
  refine ⟨hsupp, by simp, rfl, ?_⟩
  rw [getD_append_length]
  exact hm

lemma indNs_append_nil (s : ℕ) (P : List ℕ) (m p : ℕ) : indNs s (P ++ [m]) P.length p = 0 := by
  unfold indNs
  rw [if_neg]
  rintro ⟨-, h, -, -⟩
  simp at h

/-- A final block `m ≥ s + 2` after the prefix `P`, right orientation. -/
lemma indFRs_append (s : ℕ) (P : List ℕ) (m : ℕ) (hsupp : Supp (P ++ [m])) (hm : s + 2 ≤ m) :
    indFRs s (P ++ [m]) P.length (m - s) = 1 := by
  unfold indFRs
  rw [if_pos]
  refine ⟨hsupp, by simp, ?_, ?_⟩
  · rw [getD_append_length]
  · rw [getD_append_length]
    exact hm

/-- The child of a selected occurrence is a support composition. -/
lemma indNs_supp_child {s : ℕ} (hs : 2 ≤ s) {c : List ℕ} {i p : ℕ} (h : indNs s c i p = 1) :
    Supp (splitAt c i p) := by
  obtain ⟨hsupp, -, hp, hm⟩ := indNs_eq_one h
  exact Supp_splitAt c i p hsupp (by omega) (by omega)

lemma indFLs_supp_child {s : ℕ} (hs : 2 ≤ s) {c : List ℕ} {i p : ℕ} (h : indFLs s c i p = 1) :
    Supp (splitAt c i p) := by
  obtain ⟨hsupp, -, hp, hm⟩ := indFLs_eq_one h
  exact Supp_splitAt c i p hsupp (by omega) (by omega)

lemma indFRs_supp_child {s : ℕ} (hs : 2 ≤ s) {c : List ℕ} {i p : ℕ} (h : indFRs s c i p = 1) :
    Supp (splitAt c i p) := by
  obtain ⟨hsupp, -, hp, hm⟩ := indFRs_eq_one h
  exact Supp_splitAt c i p hsupp (by omega) (by omega)

lemma indNs_mul_G_nonneg {s : ℕ} (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ) :
    0 ≤ indNs s c i p * G (splitAt c i p) := by
  rcases indNs_cases s c i p with h | h
  · rw [h, zero_mul]
  · rw [h, one_mul]
    exact G_nonneg _ (indNs_supp_child hs h)

lemma indFLs_mul_G_nonneg {s : ℕ} (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ) :
    0 ≤ indFLs s c i p * G (splitAt c i p) := by
  rcases indFLs_cases s c i p with h | h
  · rw [h, zero_mul]
  · rw [h, one_mul]
    exact G_nonneg _ (indFLs_supp_child hs h)

lemma indFRs_mul_G_nonneg {s : ℕ} (hs : 2 ≤ s) (c : List ℕ) (i p : ℕ) :
    0 ≤ indFRs s c i p * G (splitAt c i p) := by
  rcases indFRs_cases s c i p with h | h
  · rw [h, zero_mul]
  · rw [h, one_mul]
    exact G_nonneg _ (indFRs_supp_child hs h)

/-! ### The raw debits are nonnegative, and the keys are injective -/

lemma LeftSource.rawDebit_nonneg (s : LeftSource) (N : ℕ) (hv : s.Valid N) : 0 ≤ s.rawDebit := by
  obtain ⟨hP, hS, ht, -⟩ := hv
  unfold LeftSource.rawDebit
  rw [LeftSource.occ_child]
  exact mul_nonneg (by norm_num)
    (G_nonneg _ (supp_append.2 ⟨hP, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨ht, hS⟩⟩⟩))

lemma Source.rawDebit_nonneg (s : Source) (N : ℕ) (hv : s.Valid N) : 0 ≤ s.rawDebit := by
  obtain ⟨hP, ht, -⟩ := hv
  unfold Source.rawDebit
  rw [Source.occ_child]
  exact mul_nonneg (by norm_num)
    (G_nonneg _ (supp_append.2 ⟨hP, supp_cons.2 ⟨ht, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩))

lemma LeftSource.eAC_injective : Function.Injective LeftSource.eAC := by
  rintro ⟨P, t, S⟩ ⟨P', t', S'⟩ h
  simp only [LeftSource.eAC, PEdge.mk.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq] at h3
  obtain ⟨rfl, h4, rfl⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

lemma LeftSource.eCD_injective : Function.Injective LeftSource.eCD := by
  rintro ⟨P, t, S⟩ ⟨P', t', S'⟩ h
  simp only [LeftSource.eCD, PEdge.mk.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj h1 (by omega)
  simp only [List.cons.injEq, true_and] at h3
  obtain ⟨rfl, h4, rfl⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

lemma Source.eAC_injective : Function.Injective Source.eAC := by
  rintro ⟨P, t⟩ ⟨P', t'⟩ h
  simp only [Source.eAC, PEdge.mk.injEq] at h
  obtain ⟨h1, h2, h5⟩ := h
  have h3 := List.append_inj h1 h2
  obtain ⟨rfl, -⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

/-! ### The cancellation of the `F_4` occurrences -/

/-- The squares of the left sources put at least `48 G(child)` on the edge
of every nonfinal and final-left `F_4` occurrence. -/
theorem LAB_ge (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) :
    48 * G (splitAt c i p) * (indNs 4 c i p + indFLs 4 c i p) ≤ LAB N c i p := by
  rw [LAB_apply]
  have hR : ∀ s ∈ leftSources N, 0 ≤ s.rawDebit :=
    fun s hs => s.rawDebit_nonneg N (mem_leftSources.1 hs)
  have key : ∀ tag : Tag, tag ≠ .finalRight → (⟨4, tag, c, i⟩ : Occ).Selected →
      (⟨4, tag, c, i⟩ : Occ).offset = p →
      48 * G (splitAt c i p)
        ≤ ∑ s ∈ leftSources N, s.rawDebit * (if s.eAB = ⟨c, i, p⟩ then 1 else 0) := by
    intro tag htag hsel hoff
    obtain ⟨s, hv, hocc⟩ := (selected_left_F4_iff N ⟨4, tag, c, i⟩).1 ⟨hsel, rfl, htag, hN⟩
    have hk : s.eAB = ⟨c, i, p⟩ := by
      rw [s.eAB_eq, hocc, Occ.edge, hoff]
    have hR' : s.rawDebit = 48 * G (splitAt c i p) := by
      rw [LeftSource.rawDebit, hocc, Occ.child, hoff]
    rw [← hR']
    exact sum_key_ge _ _ _ _ hR s (mem_leftSources.2 hv) hk
  rcases indNs_cases 4 c i p with hn | hn <;> rcases indFLs_cases 4 c i p with hl | hl
  · rw [hn, hl, add_zero, mul_zero]
    exact sum_key_nonneg _ _ _ _ hR
  · have h := (indFLs_eq_one_iff 4 ⟨by norm_num, by norm_num⟩ c i p).1 hl
    rw [hn, hl, zero_add, mul_one]
    exact key .finalLeft (by decide) h.1 h.2
  · have h := (indNs_eq_one_iff 4 ⟨by norm_num, by norm_num⟩ c i p).1 hn
    rw [hn, hl, add_zero, mul_one]
    exact key .nonfinal (by decide) h.1 h.2
  · exfalso
    have h1 := (indNs_eq_one hn).2.1
    have h2 := (indFLs_eq_one hl).2.1
    omega

/-- The squares of the final-right sources put at least `48 G(child)` on
the edge of every final-right `F_4` occurrence. -/
theorem RAB_ge (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) :
    48 * G (splitAt c i p) * indFRs 4 c i p ≤ RAB N c i p := by
  rw [RAB_apply]
  have hR : ∀ s ∈ rightSources N, 0 ≤ s.rawDebit :=
    fun s hs => s.rawDebit_nonneg N (mem_rightSources.1 hs)
  rcases indFRs_cases 4 c i p with hr | hr
  · rw [hr, mul_zero]
    exact sum_key_nonneg _ _ _ _ hR
  · obtain ⟨hsel, hoff⟩ := (indFRs_eq_one_iff 4 ⟨by norm_num, by norm_num⟩ c i p).1 hr
    obtain ⟨s, hv, hocc⟩ :=
      (selected_finalRight_F4_iff N ⟨4, .finalRight, c, i⟩).1 ⟨hsel, rfl, rfl, hN⟩
    have hk : s.eAB = ⟨c, i, p⟩ := by
      rw [s.eAB_eq, hocc, Occ.edge, hoff]
    have hR' : s.rawDebit = 48 * G (splitAt c i p) := by
      rw [Source.rawDebit, hocc, Occ.child, hoff]
    rw [hr, mul_one, ← hR']
    exact sum_key_ge _ _ _ _ hR s (mem_rightSources.2 hv) hk

/-! ### The positive additions -/

theorem LBD_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ LBD N c i p := by
  rw [LBD_apply]
  exact sum_key_nonneg _ _ _ _ fun s hs => s.rawDebit_nonneg N (mem_leftSources.1 hs)

theorem RBD_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ RBD N c i p := by
  rw [RBD_apply]
  exact sum_key_nonneg _ _ _ _ fun s hs => s.rawDebit_nonneg N (mem_rightSources.1 hs)

theorem RPOS_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ RPOS N c i p := by
  rw [RPOS_apply]
  exact sum_nonneg fun s hs =>
    mul_nonneg (s.rawDebit_nonneg N (mem_rightSources.1 hs)) (posFlow_nonneg _ _ _ _ _)

/-! ### The charges of rows 1–3 -/

/-- Normalized amount of row 1 on a nonfinal block `m`: `12(t+2)(t-1)` with
`t = m - 4`; no charge if `m < 6`. -/
def a1n (m : ℕ) : ℚ := if 6 ≤ m then 12 * ((m : ℚ) - 2) * ((m : ℚ) - 5) else 0

/-- Normalized amount of row 1 on a final block `m`: `12 t(t-1)` with
`t = m - 4`; no charge if `m < 6`. -/
def a1f (m : ℕ) : ℚ := if 6 ≤ m then 12 * ((m : ℚ) - 4) * ((m : ℚ) - 5) else 0

/-- Normalized amount of row 3 on a final block `m`: `24(t+2)(t-1)` with
`t = m - 4`; no charge if `m < 6`. -/
def a3 (m : ℕ) : ℚ := if 6 ≤ m then 24 * ((m : ℚ) - 2) * ((m : ℚ) - 5) else 0

lemma a1n_nonneg (m : ℕ) : 0 ≤ a1n m := by
  unfold a1n
  split_ifs with h
  · have h6 : (6 : ℚ) ≤ m := by exact_mod_cast h
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  · exact le_refl 0

lemma a1f_nonneg (m : ℕ) : 0 ≤ a1f m := by
  unfold a1f
  split_ifs with h
  · have h6 : (6 : ℚ) ≤ m := by exact_mod_cast h
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  · exact le_refl 0

lemma a3_nonneg (m : ℕ) : 0 ≤ a3 m := by
  unfold a3
  split_ifs with h
  · have h6 : (6 : ℚ) ≤ m := by exact_mod_cast h
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  · exact le_refl 0

/-- **Row 1.**  The total charge on an edge from the edges `A → C` of the
left squares is at most the normalized amount of row 1 times `G(child)` if
the edge carries a left `F_2` occurrence, and at most zero on any other
edge.  With `LAC_nonneg` it vanishes there (`LAC_eq_zero_of_not`). -/
theorem LAC_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LAC N c i p ≤ (indNs 2 c i p * a1n (c.getD i 0) + indFLs 2 c i p * a1f (c.getD i 0))
      * G (splitAt c i p) := by
  rw [LAC_apply]
  refine sum_key_le _ _ _ _ _ (fun s _ s' _ h => LeftSource.eAC_injective h) ?_ ?_
  · have h1 := mul_nonneg (a1n_nonneg (c.getD i 0))
      (indNs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p)
    have h2 := mul_nonneg (a1f_nonneg (c.getD i 0))
      (indFLs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p)
    nlinarith [h1, h2]
  · rintro ⟨P, t, S⟩ hs hk
    obtain ⟨hP, hS, ht, -⟩ := mem_leftSources.1 hs
    simp only at hP hS ht
    simp only [LeftSource.eAC, PEdge.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have hsupp : Supp (P ++ (t + 4) :: S) := supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, hS⟩⟩
    have e : t + 4 - 2 = t + 2 := by omega
    have hcast : (((t + 4 : ℕ) : ℚ)) = (t : ℚ) + 4 := by push_cast; ring
    rw [LeftSource.rawDebit, LeftSource.occ_child]
    show 48 * G (P ++ 4 :: t :: S) ≤ _
    rw [getD_append_length, splitAt_append, e]
    by_cases hS' : S = []
    · subst hS'
      rw [indNs_append_nil, indFLs_append 2 P (t + 4) hsupp (by omega), amount_AC_final P t ht]
      unfold a1f
      rw [if_pos (by omega), hcast]
      apply le_of_eq
      ring
    · rw [indNs_append 2 P S (t + 4) hsupp hS' (by omega),
        indFLs_append_of_ne 2 P S (t + 4) 2 hS', amount_AC_nonfinal P S t ht hS']
      unfold a1n
      rw [if_pos (by omega), hcast]
      apply le_of_eq
      ring

/-- **Row 2.**  The total charge from the edges `C → D` of the left squares
is at most `24 G(child)` if the edge carries a left `F_2` occurrence, and at
most zero on any other edge.  With `LCD_nonneg` it vanishes there
(`LCD_eq_zero_of_not`). -/
theorem LCD_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LCD N c i p ≤ (indNs 2 c i p + indFLs 2 c i p) * 24 * G (splitAt c i p) := by
  rw [LCD_apply]
  refine sum_key_le _ _ _ _ _ (fun s _ s' _ h => LeftSource.eCD_injective h) ?_ ?_
  · nlinarith [indNs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p,
      indFLs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p]
  · rintro ⟨P, t, S⟩ hs hk
    obtain ⟨hP, hS, ht, -⟩ := mem_leftSources.1 hs
    simp only at hP hS ht
    simp only [LeftSource.eCD, PEdge.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have hsupp : Supp ((P ++ [2]) ++ (t + 2) :: S) :=
      supp_append.2 ⟨supp_append.2 ⟨hP, supp_cons.2 ⟨le_refl 2, supp_nil⟩⟩,
        supp_cons.2 ⟨by omega, hS⟩⟩
    have e : t + 2 - 2 = t := by omega
    have hlist : (P ++ [2]) ++ (t + 2) :: S = P ++ 2 :: (t + 2) :: S := by simp
    have hlen : (P ++ [2]).length = P.length + 1 := by simp
    rw [LeftSource.rawDebit, LeftSource.occ_child]
    show 48 * G (P ++ 4 :: t :: S) ≤ _
    rw [splitAt_append_succ, e, amount_CD]
    by_cases hS' : S = []
    · subst hS'
      have h1 := indNs_append_nil 2 (P ++ [2]) (t + 2) 2
      have h2 := indFLs_append 2 (P ++ [2]) (t + 2) hsupp (by omega)
      rw [hlist, hlen] at h1 h2
      rw [h1, h2]
      apply le_of_eq
      ring
    · have h1 := indNs_append 2 (P ++ [2]) S (t + 2) hsupp hS' (by omega)
      have h2 := indFLs_append_of_ne 2 (P ++ [2]) S (t + 2) 2 hS'
      rw [hlist, hlen] at h1 h2
      rw [h1, h2]
      apply le_of_eq
      ring

/-- **Row 3.**  The total charge from the edges `A → C` of the final-right
squares is at most the normalized amount of row 3 times `G(child)` if the
edge carries a right `F_2` occurrence, and at most zero on any other edge.
With `RAC_nonneg` it vanishes there (`RAC_eq_zero_of_not`). -/
theorem RAC_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RAC N c i p ≤ indFRs 2 c i p * a3 (c.getD i 0) * G (splitAt c i p) := by
  rw [RAC_apply]
  refine sum_key_le _ _ _ _ _ (fun s _ s' _ h => Source.eAC_injective h) ?_ ?_
  · have h := mul_nonneg (a3_nonneg (c.getD i 0))
      (indFRs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p)
    nlinarith [h]
  · rintro ⟨P, t⟩ hs hk
    obtain ⟨hP, ht, -⟩ := mem_rightSources.1 hs
    simp only at hP ht
    simp only [Source.eAC, PEdge.mk.injEq] at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    have hsupp : Supp (P ++ [t + 4]) := supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, supp_nil⟩⟩
    have e1 : t + 4 - 2 = t + 2 := by omega
    have e2 : t + 4 - (t + 2) = 2 := by omega
    have hcast : (((t + 4 : ℕ) : ℚ)) = (t : ℚ) + 4 := by push_cast; ring
    have h1 := indFRs_append 2 P (t + 4) hsupp (by omega)
    rw [e1] at h1
    rw [Source.rawDebit, Source.occ_child]
    show 48 * G (P ++ [t, 4]) ≤ _
    rw [getD_append_length, splitAt_append, e2, h1, amount_right_AC P t ht]
    unfold a3
    rw [if_pos (by omega), hcast]
    apply le_of_eq
    ring

/-! ### The charges of rows 4–6 -/

lemma chargeAt_edge_injective {Q Q' : List ℕ} {y y' : ℕ}
    (h : (chargeAt Q y).label.edge = (chargeAt Q' y').label.edge) : Q = Q' ∧ y = y' := by
  have hp : (chargeAt Q y).label.parent = (chargeAt Q' y').label.parent :=
    congrArg PEdge.parent h
  have hi : (chargeAt Q y).label.idx = (chargeAt Q' y').label.idx := congrArg PEdge.idx h
  rw [chargeAt_label_parent, chargeAt_label_parent] at hp
  rw [chargeAt_label_idx, chargeAt_label_idx] at hi
  have h3 := List.append_inj hp hi
  simp only [List.cons.injEq, and_true] at h3
  exact ⟨h3.1, by omega⟩

/-- The edge of the charge at `Q.(y+2,2)`: offset `3` for the `F_3` label
(`y = 3`), offset `2` for the `F_2` labels. -/
lemma chargeAt_edge (Q : List ℕ) (y : ℕ) :
    (chargeAt Q y).label.edge = ⟨Q ++ [y + 2, 2], Q.length, if y = 3 then 3 else 2⟩ := by
  unfold chargeAt
  split_ifs with h1 h2
  · subst h1
    rfl
  · subst h2
    rfl
  · rfl

lemma RCH_le_of_charge (N : ℕ) (c : List ℕ) (i p : ℕ) (Q : List ℕ) (y : ℕ) (hQ : Supp Q)
    (hy : 2 ≤ y) (hN : Q.sum + y + 4 = N) (hedge : (chargeAt Q y).label.edge = ⟨c, i, p⟩) :
    RCH N c i p ≤ (indNs 2 c i p * 75 + indNs 3 c i p * 60) * G (splitAt c i p) := by
  have hiff : ∀ s' : Source, ∀ ch' ∈ s'.trace,
      (ch'.label.edge = ⟨c, i, p⟩ ↔ ch' = chargeAt Q y) := by
    intro s' ch' hch'
    constructor
    · intro he
      obtain ⟨j', y', -, -, rfl⟩ := (mem_trace_iff s' ch').1 hch'
      obtain ⟨h1, h2⟩ := chargeAt_edge_injective (he.trans hedge.symm)
      rw [h1, h2]
    · rintro rfl
      exact hedge
  have hsum : RCH N c i p
      = ∑ s' ∈ (validSources_finite N).toFinset,
          (s'.trace.count (chargeAt Q y) : ℚ) * s'.rawDebit := by
    rw [RCH_apply]
    exact sum_congr rfl fun s' _ => by
      rw [chargeFlow_eq_count _ _ _ _ _ (hiff s'), mul_comm]
  have hchild : (chargeAt Q y).label.child = splitAt c i p := congrArg PEdge.child hedge
  have hsuppX : Supp (Q ++ [y + 2, 2]) :=
    supp_append.2 ⟨hQ, supp_cons.2 ⟨by omega, supp_cons.2 ⟨le_refl 2, supp_nil⟩⟩⟩
  rw [chargeAt_edge] at hedge
  simp only [PEdge.mk.injEq] at hedge
  obtain ⟨rfl, rfl, hp⟩ := hedge
  rw [hsum]
  by_cases h3 : y = 3
  · subst h3
    have hlt := total_charge_F3_lt N Q hQ hN
    rw [hchild] at hlt
    rw [if_pos rfl] at hp
    subst hp
    have hn3 : indNs 3 (Q ++ [3 + 2, 2]) Q.length 3 = 1 :=
      indNs_append 3 Q [2] (3 + 2) hsuppX (by simp) (by norm_num)
    have hn2 := indNs_mul_G_nonneg (by norm_num : 2 ≤ 2) (Q ++ [3 + 2, 2]) Q.length 3
    rw [hn3]
    nlinarith [hlt, hn2]
  · have hle := total_charge_le N Q y hQ hy hN
    rw [hchild] at hle
    rw [if_neg h3] at hp
    subst hp
    have hn2 : indNs 2 (Q ++ [y + 2, 2]) Q.length 2 = 1 :=
      indNs_append 2 Q [2] (y + 2) hsuppX (by simp) (by omega)
    have hn3 := indNs_mul_G_nonneg (by norm_num : 2 ≤ 3) (Q ++ [y + 2, 2]) Q.length 2
    rw [hn2]
    nlinarith [hle, hn3]

/-- **Rows 4–6.**  All cascades together charge at most `75 G(child)` to an
edge that carries a nonfinal `F_2` occurrence, at most `60 G(child)` to an
edge that carries a nonfinal `F_3` occurrence, and at most zero to any other
edge.  With `RCH_nonneg` the charge vanishes there (`RCH_eq_zero_of_not`). -/
theorem RCH_le (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RCH N c i p ≤ (indNs 2 c i p * 75 + indNs 3 c i p * 60) * G (splitAt c i p) := by
  by_cases h : ∃ s ∈ rightSources N, ∃ ch ∈ s.trace, ch.label.edge = ⟨c, i, p⟩
  · obtain ⟨s, hs, ch, hch, hedge⟩ := h
    obtain ⟨hP, ht, hsum⟩ := mem_rightSources.1 hs
    obtain ⟨j, y, hy, hty, rfl⟩ := (mem_trace_iff s ch).1 hch
    refine RCH_le_of_charge N c i p (s.P ++ List.replicate j 2) y ?_ hy ?_ hedge
    · exact supp_append.2 ⟨hP, fun m hm => by
        have := List.eq_of_mem_replicate hm
        omega⟩
    · rw [List.sum_append, List.sum_replicate, smul_eq_mul]
      omega
  · rw [RCH_apply, sum_eq_zero fun s hs => by
      rw [chargeFlow_eq_zero _ _ _ _ (fun ch hch he => h ⟨s, hs, ch, hch, he⟩), mul_zero]]
    nlinarith [indNs_mul_G_nonneg (by norm_num : 2 ≤ 2) c i p,
      indNs_mul_G_nonneg (by norm_num : 2 ≤ 3) c i p]

/-! ### Lower bounds for the reserve (35) -/

lemma vq_nonneg (n : ℕ) (h : 2 ≤ n) : 0 ≤ vq n := by
  unfold vq
  have : (2 : ℚ) ≤ n := by exact_mod_cast h
  exact mul_nonneg (by linarith) (by linarith)

lemma V_nonneg (c : List ℕ) (hs : Supp c) : 0 ≤ V c := by
  induction c with
  | nil => simp [V]
  | cons a l ih =>
    rw [V_cons]
    exact add_nonneg (vq_nonneg a (hs a List.mem_cons_self))
      (ih fun m hm => hs m (List.mem_cons_of_mem a hm))

/-- `V` is at least the contribution of any one block. -/
lemma vq_le_V (c : List ℕ) (hs : Supp c) (x : ℕ) (hx : x ∈ c) : vq x ≤ V c := by
  induction c with
  | nil => cases hx
  | cons a l ih =>
    have hl : Supp l := fun m hm => hs m (List.mem_cons_of_mem a hm)
    rw [V_cons]
    rcases List.mem_cons.1 hx with h | h
    · rw [h]
      linarith [V_nonneg l hl]
    · linarith [ih hl h, vq_nonneg a (hs a List.mem_cons_self)]

lemma two_blocks_le_sum (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    c.getD i 0 + c.getD (i + 1) 0 ≤ c.sum := by
  have hd := decomp_at2 c i hi
  have h : c.sum
      = (c.take i).sum + (c.getD i 0 + (c.getD (i + 1) 0 + (c.drop (i + 2)).sum)) := by
    conv_lhs => rw [hd]
    simp only [List.sum_append, List.sum_cons]
  omega

lemma vq_sub_two (m : ℕ) (hm : 2 ≤ m) : vq (m - 2) = ((m : ℚ) - 2) * ((m : ℚ) - 4) := by
  unfold vq
  rw [Nat.cast_sub hm]
  push_cast
  ring

/-- Nonfinal left `F_2` occurrence of a block `M`: the reserve (35) minus
the largest possible charges of rows 1, 2 and 4–5 is nonnegative.  With
`V(child) ≥ (M-2)(M-4)` and `N ≥ M + 2` the difference is at least
`18M^2 - 66M + 69` for `M ≥ 6`; the cases `M = 4, 5` are included.  The
manuscript states the strict inequality; `≥ 0` is what nonnegativity uses. -/
lemma margin_N2 (c : List ℕ) (i p : ℕ) (h : indNs 2 c i p = 1) :
    0 ≤ 30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a1n (c.getD i 0) - 99 := by
  obtain ⟨hsupp, hi, rfl, hm⟩ := indNs_eq_one h
  have hch : Supp (splitAt c i 2) := Supp_splitAt c i 2 hsupp (by norm_num) (by omega)
  have hV := vq_le_V _ hch _ (rest_mem_splitAt c i 2)
  have hb := hsupp _ (getD_mem c (i + 1) hi)
  have hsum := two_blocks_le_sum c i hi
  have hN : (c.getD i 0 : ℚ) + 2 ≤ (c.sum : ℚ) := by
    exact_mod_cast (by omega : c.getD i 0 + 2 ≤ c.sum)
  have hx : (4 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast hm
  rw [vq_sub_two _ (by omega)] at hV
  unfold a1n
  split_ifs with h6
  · have hx6 : (6 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast h6
    nlinarith [mul_nonneg (sub_nonneg.2 hx6) (sub_nonneg.2 hx6)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)]

/-- Final-left `F_2` occurrence of a block `M`: the reserve (35) minus the
largest possible charges of rows 1 and 2 is nonnegative.  With
`V(child) ≥ (M-2)(M-4)` and `N ≥ M` the difference is at least
`18M^2 - 42M - 36` for `M ≥ 6`; the cases `M = 4, 5` are included. -/
lemma margin_FL2 (c : List ℕ) (i p : ℕ) (h : indFLs 2 c i p = 1) :
    0 ≤ 30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a1f (c.getD i 0) - 24 := by
  obtain ⟨hsupp, hi, rfl, hm⟩ := indFLs_eq_one h
  have hlt : i < c.length := by omega
  have hch : Supp (splitAt c i 2) := Supp_splitAt c i 2 hsupp (by norm_num) (by omega)
  have hV := vq_le_V _ hch _ (rest_mem_splitAt c i 2)
  have hN : (c.getD i 0 : ℚ) ≤ (c.sum : ℚ) := by
    exact_mod_cast mem_le_sum (getD_mem c i hlt)
  have hx : (4 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast hm
  rw [vq_sub_two _ (by omega)] at hV
  unfold a1f
  split_ifs with h6
  · have hx6 : (6 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast h6
    nlinarith [mul_nonneg (sub_nonneg.2 hx6) (sub_nonneg.2 hx6)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)]

/-- Final-right `F_2` occurrence of a block `M`: the reserve (35) minus the
largest possible charge of row 3 is nonnegative.  With
`V(child) ≥ (M-2)(M-4)` and `N ≥ M` the difference is at least
`6M^2 + 18M - 12` for `M ≥ 6`; the cases `M = 4, 5` are included. -/
lemma margin_FR2 (c : List ℕ) (i p : ℕ) (h : indFRs 2 c i p = 1) :
    0 ≤ 30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a3 (c.getD i 0) := by
  obtain ⟨hsupp, hi, rfl, hm⟩ := indFRs_eq_one h
  have hlt : i < c.length := by omega
  have hch : Supp (splitAt c i (c.getD i 0 - 2)) :=
    Supp_splitAt c i _ hsupp (by omega) (by omega)
  have hV := vq_le_V _ hch _ (p_mem_splitAt c i (c.getD i 0 - 2))
  have hN : (c.getD i 0 : ℚ) ≤ (c.sum : ℚ) := by
    exact_mod_cast mem_le_sum (getD_mem c i hlt)
  have hx : (4 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast hm
  rw [vq_sub_two _ (by omega)] at hV
  unfold a3
  split_ifs with h6
  · have hx6 : (6 : ℚ) ≤ (c.getD i 0 : ℚ) := by exact_mod_cast h6
    nlinarith [mul_nonneg (sub_nonneg.2 hx6) (sub_nonneg.2 hx6)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)]

/-! ### Proposition 8.2 -/

/-- **Proposition 8.2 (uniform nonnegativity).**  On the compositions of
`N`, every edge value of `f_d` is nonnegative.  The manuscript states this
for `d ≥ 3`, `N = d + 2`; the proof needs no condition on `N`. -/
theorem fd_nonneg (N : ℕ) (c : List ℕ) (i p : ℕ) (hN : c.sum = N) : 0 ≤ fd N c i p := by
  rw [fd_apply, f0_eq]
  have hLAB := LAB_ge N c i p hN
  have hRAB := RAB_ge N c i p hN
  have hLBD := LBD_nonneg N c i p
  have hRBD := RBD_nonneg N c i p
  have hRPOS := RPOS_nonneg N c i p
  have hLAC := LAC_le N c i p
  have hLCD := LCD_le N c i p
  have hRAC := RAC_le N c i p
  have hRCH := RCH_le N c i p
  have t1 : 0 ≤ indNs 2 c i p
      * (30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a1n (c.getD i 0) - 99)
      * G (splitAt c i p) := by
    rcases indNs_cases 2 c i p with h | h
    · rw [h, zero_mul, zero_mul]
    · rw [h, one_mul]
      exact mul_nonneg (margin_N2 c i p h) (G_nonneg _ (indNs_supp_child (by norm_num) h))
  have t2 : 0 ≤ indFLs 2 c i p
      * (30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a1f (c.getD i 0) - 24)
      * G (splitAt c i p) := by
    rcases indFLs_cases 2 c i p with h | h
    · rw [h, zero_mul, zero_mul]
    · rw [h, one_mul]
      exact mul_nonneg (margin_FL2 c i p h) (G_nonneg _ (indFLs_supp_child (by norm_num) h))
  have t3 : 0 ≤ indFRs 2 c i p
      * (30 * V (splitAt c i p) + 30 * (c.sum : ℚ) - 12 - a3 (c.getD i 0))
      * G (splitAt c i p) := by
    rcases indFRs_cases 2 c i p with h | h
    · rw [h, zero_mul, zero_mul]
    · rw [h, one_mul]
      exact mul_nonneg (margin_FR2 c i p h) (G_nonneg _ (indFRs_supp_child (by norm_num) h))
  have t4 := indNs_mul_G_nonneg (by norm_num : 2 ≤ 3) c i p
  have t5 := indFLs_mul_G_nonneg (by norm_num : 2 ≤ 3) c i p
  have t6 := indFRs_mul_G_nonneg (by norm_num : 2 ≤ 3) c i p
  unfold ind
  nlinarith [hLAB, hRAB, hLBD, hRBD, hRPOS, hLAC, hLCD, hRAC, hRCH, t1, t2, t3, t4, t5, t6]

end K4
end ChowCone
