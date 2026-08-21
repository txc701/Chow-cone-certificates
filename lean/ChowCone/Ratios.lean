/-
The three G-ratio identities (Draft Lemma 5 / frozen Lemma 1).

Stated first in abstract `l₁ ++ m :: l₂` form (no index plumbing), then in
positional `splitAt` form as used by the divergence computation.
-/
import ChowCone.Flow

namespace ChowCone

/-! ### Scalar cores (pure factorial algebra, `m = k + 4`) -/

lemma factorial_k4 (k : ℕ) :
    (Nat.factorial (k + 4) : ℚ)
      = ((k : ℚ) + 4) * ((k : ℚ) + 3) * (Nat.factorial (k + 2) : ℚ) := by
  have h1 : Nat.factorial (k + 4) = (k + 4) * Nat.factorial (k + 3) :=
    Nat.factorial_succ (k + 3)
  have h2 : Nat.factorial (k + 3) = (k + 3) * Nat.factorial (k + 2) :=
    Nat.factorial_succ (k + 2)
  rw [h1, h2]
  push_cast
  ring

lemma blockTerm_two : blockTerm 2 = 1 / 2 := by
  norm_num [blockTerm, partQ, factQ, Nat.factorial]

/-- Scalar core of ratio (N): `bt(2)·bt(m−2) = ρ(m)·bt(m)` for `m ≥ 4`. -/
lemma scalar_N (m : ℕ) (h4 : 4 ≤ m) :
    blockTerm 2 * blockTerm (m - 2) = rho m * blockTerm m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  have e1 : 4 + k - 2 = k + 2 := by omega
  have e2 : 4 + k = k + 4 := by omega
  rw [e1, e2, blockTerm_two]
  unfold blockTerm rho partQ factQ
  rw [factorial_k4]
  have hne : (Nat.factorial (k + 2) : ℚ) ≠ 0 := factorial_cast_ne_zero _
  have h3 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h4' : ((k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Scalar core of ratio (FL):
`(m−2)·bt(2)·bt(m−2) = ((m−2)(m−3)/2)·m·bt(m)` for `m ≥ 4`. -/
lemma scalar_FL (m : ℕ) (h4 : 4 ≤ m) :
    ((m : ℚ) - 2) * (blockTerm 2 * blockTerm (m - 2))
      = (((m : ℚ) - 2) * ((m : ℚ) - 3) / 2) * ((m : ℚ) * blockTerm m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  have e1 : 4 + k - 2 = k + 2 := by omega
  have e2 : 4 + k = k + 4 := by omega
  rw [e1, e2, blockTerm_two]
  unfold blockTerm partQ factQ
  rw [factorial_k4]
  have hne : (Nat.factorial (k + 2) : ℚ) ≠ 0 := factorial_cast_ne_zero _
  have h3 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h4' : ((k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Scalar core of ratio (FR):
`2·bt(m−2)·bt(2) = (m−3)·m·bt(m)` for `m ≥ 4`. -/
lemma scalar_FR (m : ℕ) (h4 : 4 ≤ m) :
    2 * (blockTerm (m - 2) * blockTerm 2)
      = ((m : ℚ) - 3) * ((m : ℚ) * blockTerm m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  have e1 : 4 + k - 2 = k + 2 := by omega
  have e2 : 4 + k = k + 4 := by omega
  rw [e1, e2, blockTerm_two]
  unfold blockTerm partQ factQ
  rw [factorial_k4]
  have hne : (Nat.factorial (k + 2) : ℚ) ≠ 0 := factorial_cast_ne_zero _
  have h3 : ((k : ℚ) + 4) ≠ 0 := by positivity
  have h4' : ((k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-! ### Abstract-form ratio lemmas -/

/-- Ratio (N), abstract form: the split block is nonfinal (`l₂ ≠ []`). -/
lemma G_ratio_N (l₁ l₂ : List ℕ) (m : ℕ) (h4 : 4 ≤ m) (h2 : l₂ ≠ []) :
    G (l₁ ++ 2 :: (m - 2) :: l₂) = rho m * G (l₁ ++ m :: l₂) := by
  unfold G
  have hsum : (l₁ ++ 2 :: (m - 2) :: l₂).sum = (l₁ ++ m :: l₂).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast : lastPart (l₁ ++ 2 :: (m - 2) :: l₂) = lastPart (l₁ ++ m :: l₂) := by
    rw [lastPart_append_cons_of_ne _ _ _ (by simp [h2]),
        lastPart_append_cons_of_ne _ _ _ h2]
    rw [show ((m - 2) :: l₂ : List ℕ) = [] ++ (m - 2) :: l₂ from rfl,
        lastPart_append_cons_of_ne _ _ _ h2]
  rw [hlast]
  have hg : gprod (l₁ ++ 2 :: (m - 2) :: l₂)
      = gprod l₁ * (blockTerm 2 * blockTerm (m - 2)) * gprod l₂ := by
    rw [show (l₁ ++ 2 :: (m - 2) :: l₂ : List ℕ)
        = l₁ ++ (2 :: (m - 2) :: l₂) from rfl, gprod_append]
    rw [gprod_cons, gprod_cons]
    ring
  have hg' : gprod (l₁ ++ m :: l₂) = gprod l₁ * blockTerm m * gprod l₂ := by
    rw [gprod_append, gprod_cons]; ring
  rw [hg, hg', scalar_N m h4]
  ring

/-- Ratio (FL), abstract form: split of the final block, left peel. -/
lemma G_ratio_FL (l₁ : List ℕ) (m : ℕ) (h4 : 4 ≤ m) :
    G (l₁ ++ 2 :: [m - 2])
      = (((m : ℚ) - 2) * ((m : ℚ) - 3) / 2) * G (l₁ ++ [m]) := by
  unfold G
  have hsum : (l₁ ++ 2 :: [m - 2]).sum = (l₁ ++ [m]).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast1 : lastPart (l₁ ++ 2 :: [m - 2]) = m - 2 := by
    rw [show (l₁ ++ 2 :: [m - 2] : List ℕ) = (l₁ ++ [2]) ++ [m - 2] by simp,
        lastPart_append_cons_nil]
  have hlast2 : lastPart (l₁ ++ [m]) = m := lastPart_append_cons_nil l₁ m
  rw [hlast1, hlast2]
  have hg : gprod (l₁ ++ 2 :: [m - 2])
      = gprod l₁ * (blockTerm 2 * blockTerm (m - 2)) := by
    rw [gprod_append, gprod_cons, gprod_cons, gprod_nil]
    ring
  have hg' : gprod (l₁ ++ [m]) = gprod l₁ * blockTerm m := by
    rw [gprod_append, gprod_cons, gprod_nil]
    ring
  rw [hg, hg']
  have hm2 : ((m - 2 : ℕ) : ℚ) = (m : ℚ) - 2 := by
    have : (2 : ℕ) ≤ m := by omega
    push_cast [this]
    ring
  rw [hm2]
  have key := scalar_FL m h4
  linear_combination (Nat.factorial ((l₁ ++ [m]).sum - 1) : ℚ) * gprod l₁ * key

/-- Ratio (FR), abstract form: split of the final block, right peel. -/
lemma G_ratio_FR (l₁ : List ℕ) (m : ℕ) (h4 : 4 ≤ m) :
    G (l₁ ++ (m - 2) :: [2]) = ((m : ℚ) - 3) * G (l₁ ++ [m]) := by
  unfold G
  have hsum : (l₁ ++ (m - 2) :: [2]).sum = (l₁ ++ [m]).sum := by
    simp [List.sum_append]
    omega
  rw [hsum]
  have hlast1 : lastPart (l₁ ++ (m - 2) :: [2]) = 2 := by
    rw [show (l₁ ++ (m - 2) :: [2] : List ℕ) = (l₁ ++ [m - 2]) ++ [2] by simp,
        lastPart_append_cons_nil]
  have hlast2 : lastPart (l₁ ++ [m]) = m := lastPart_append_cons_nil l₁ m
  rw [hlast1, hlast2]
  have hg : gprod (l₁ ++ (m - 2) :: [2])
      = gprod l₁ * (blockTerm (m - 2) * blockTerm 2) := by
    rw [gprod_append, gprod_cons, gprod_cons, gprod_nil]
    ring
  have hg' : gprod (l₁ ++ [m]) = gprod l₁ * blockTerm m := by
    rw [gprod_append, gprod_cons, gprod_nil]
    ring
  rw [hg, hg']
  have key := scalar_FR m h4
  linear_combination (Nat.factorial ((l₁ ++ [m]).sum - 1) : ℚ) * gprod l₁ * key

/-! ### Positional forms -/

/-- `splitAt` in decomposed coordinates (definitional unfolding). -/
lemma splitAt_eq (c : List ℕ) (i p : ℕ) :
    splitAt c i p = c.take i ++ p :: (c.getD i 0 - p) :: c.drop (i + 1) := rfl

/-- Ratio (N), positional: nonfinal block `c_i ≥ 4`, offset 2. -/
lemma G_splitAt_nonfinal (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length)
    (h4 : 4 ≤ c.getD i 0) :
    G (splitAt c i 2) = rho (c.getD i 0) * G c := by
  have hlt : i < c.length := Nat.lt_of_succ_lt hi
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) ≠ [] := by
    intro h
    have := List.drop_eq_nil_iff.1 h
    omega
  rw [splitAt_eq]
  set m := c.getD i 0 with hm
  conv_rhs => rw [hd]
  exact G_ratio_N (c.take i) (c.drop (i + 1)) m h4 hdrop

/-- Ratio (FL), positional. -/
lemma G_splitAt_final_left (c : List ℕ) (i : ℕ) (hi : i + 1 = c.length)
    (h4 : 4 ≤ c.getD i 0) :
    G (splitAt c i 2)
      = (((c.getD i 0 : ℚ) - 2) * ((c.getD i 0 : ℚ) - 3) / 2) * G c := by
  have hlt : i < c.length := by omega
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) = [] := by
    apply List.drop_eq_nil_iff.2
    omega
  rw [splitAt_eq, hdrop]
  set m := c.getD i 0 with hm
  conv_rhs => rw [hd, hdrop]
  exact G_ratio_FL (c.take i) m h4

/-- Ratio (FR), positional. -/
lemma G_splitAt_final_right (c : List ℕ) (i : ℕ) (hi : i + 1 = c.length)
    (h4 : 4 ≤ c.getD i 0) :
    G (splitAt c i (c.getD i 0 - 2)) = ((c.getD i 0 : ℚ) - 3) * G c := by
  have hlt : i < c.length := by omega
  have hd := decomp_at c i hlt
  have hdrop : c.drop (i + 1) = [] := by
    apply List.drop_eq_nil_iff.2
    omega
  have hsub : c.getD i 0 - (c.getD i 0 - 2) = 2 := by omega
  rw [splitAt_eq, hdrop, hsub]
  set m := c.getD i 0 with hm
  conv_rhs => rw [hd, hdrop]
  exact G_ratio_FR (c.take i) m h4

end ChowCone
