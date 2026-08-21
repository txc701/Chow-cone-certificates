/-
The explicit certificate flow (Draft Definition 4) and its divergence.

Correspondence (LEAN_CORRESPONDENCE.md): Draft §2 (dictionary), Definition 4,
§3 divergence conventions.  `F c i p` is the total flow on the Boolean cover
edge that splits block `i` of `c` at offset `p` — a sum of indicator terms,
one per selected move realizing the edge, so the FL/FR coincidence on a
final block 4 is handled definitionally (the edge then carries `2·G(child)`).
-/
import ChowCone.Basic

namespace ChowCone

/-- Split block `i` of `c` at offset `p` (Draft §2). -/
def splitAt (c : List ℕ) (i p : ℕ) : List ℕ :=
  c.take i ++ p :: (c.getD i 0 - p) :: c.drop (i + 1)

/-- Merge blocks `i` and `i+1` of `c` (Draft §6, reverse of a split). -/
def mergeAt (c : List ℕ) (i : ℕ) : List ℕ :=
  c.take i ++ (c.getD i 0 + c.getD (i + 1) 0) :: c.drop (i + 2)

/-- Selected-move indicator (N): nonfinal block `≥ 4`, offset 2. -/
def indN (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 < c.length ∧ p = 2 ∧ 4 ≤ c.getD i 0 then 1 else 0

/-- Selected-move indicator (FL): final block `≥ 4`, offset 2. -/
def indFL (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 = c.length ∧ p = 2 ∧ 4 ≤ c.getD i 0 then 1 else 0

/-- Selected-move indicator (FR): final block `≥ 4`, offset `c_i − 2`. -/
def indFR (c : List ℕ) (i p : ℕ) : ℚ :=
  if Supp c ∧ i + 1 = c.length ∧ p = c.getD i 0 - 2 ∧ 4 ≤ c.getD i 0 then 1 else 0

/-- The edge flow (Draft Definition 4):
`F c i p = (#selected moves realizing the edge) · G(child)`. -/
def F (c : List ℕ) (i p : ℕ) : ℚ :=
  (indN c i p + indFL c i p + indFR c i p) * G (splitAt c i p)

/-- Total outflow of `c`: sum over all splits (Draft §3). -/
def outSum (c : List ℕ) : ℚ :=
  ∑ i ∈ Finset.range c.length,
    ∑ p ∈ Finset.Icc 1 (c.getD i 0 - 1), F c i p

/-- Total inflow of `c`: every Boolean cover edge into `c` merges a unique
adjacent pair of blocks of `c` (Draft §6), so inflow is the sum over the
adjacent pairs. -/
def inSum (c : List ℕ) : ℚ :=
  ∑ i ∈ Finset.range (c.length - 1), F (mergeAt c i) i (c.getD i 0)

/-- Divergence: outflow minus inflow (Draft §3 sign convention). -/
def flowDiv (c : List ℕ) : ℚ := outSum c - inSum c

/-! ### Structural facts about splits -/

lemma splitAt_mem (c : List ℕ) (i p : ℕ) (x : ℕ) (hx : x ∈ splitAt c i p) :
    x ∈ c ∨ x = p ∨ x = c.getD i 0 - p := by
  unfold splitAt at hx
  rcases List.mem_append.1 hx with h | h
  · exact Or.inl (List.take_subset i c h)
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl (List.drop_subset (i+1) c h)

/-- Children of selected moves are support compositions. -/
lemma Supp_splitAt (c : List ℕ) (i p : ℕ) (hs : Supp c)
    (hp : 2 ≤ p) (hp2 : 2 ≤ c.getD i 0 - p) : Supp (splitAt c i p) := by
  intro x hx
  rcases splitAt_mem c i p x hx with h | h | h
  · exact hs x h
  · omega
  · omega

lemma splitAt_ne_nil (c : List ℕ) (i p : ℕ) : splitAt c i p ≠ [] := by
  unfold splitAt
  simp

/-- Each indicator vanishes unless the generic split conditions hold. -/
lemma indN_eq_zero (c : List ℕ) (i p : ℕ)
    (hc : ¬(Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p)) : indN c i p = 0 := by
  unfold indN
  rw [if_neg]
  rintro ⟨hs, _, rfl, h4⟩
  exact hc ⟨hs, by omega, by omega⟩

lemma indFL_eq_zero (c : List ℕ) (i p : ℕ)
    (hc : ¬(Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p)) : indFL c i p = 0 := by
  unfold indFL
  rw [if_neg]
  rintro ⟨hs, _, rfl, h4⟩
  exact hc ⟨hs, by omega, by omega⟩

lemma indFR_eq_zero (c : List ℕ) (i p : ℕ)
    (hc : ¬(Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p)) : indFR c i p = 0 := by
  unfold indFR
  rw [if_neg]
  rintro ⟨hs, _, rfl, h4⟩
  exact hc ⟨hs, by omega, by omega⟩

/-- Nonnegativity of the flow (Draft Definition 4). -/
theorem F_nonneg (c : List ℕ) (i p : ℕ) : 0 ≤ F c i p := by
  unfold F
  by_cases hc : Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p
  · have hG : 0 ≤ G (splitAt c i p) :=
      G_nonneg _ (Supp_splitAt c i p hc.1 hc.2.1 hc.2.2)
    have hind : 0 ≤ indN c i p + indFL c i p + indFR c i p := by
      unfold indN indFL indFR
      split_ifs <;> norm_num
    exact mul_nonneg hind hG
  · rw [indN_eq_zero c i p hc, indFL_eq_zero c i p hc, indFR_eq_zero c i p hc]
    norm_num

/-- All indicators (hence `F`) vanish on non-support compositions. -/
lemma F_eq_zero_of_not_supp (c : List ℕ) (i p : ℕ) (h : ¬ Supp c) :
    F c i p = 0 := by
  unfold F indN indFL indFR
  simp only [h, false_and, if_false]
  ring

end ChowCone
