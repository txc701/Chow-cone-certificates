/-
Basic definitions for the Cheng–Lin Conjecture 3.30 certificate.

Correspondence (LEAN_CORRESPONDENCE.md): Draft §1–§2, Definition 3, (W).
All scalars are rationals; formulas are verbatim from the frozen proof.
-/
import Mathlib

namespace ChowCone

/-- `ρ(m) = m(m−3)/2` (Draft Definition 3). `ρ(2) = −1`, `ρ(3) = 0`. -/
def rho (m : ℕ) : ℚ := (m : ℚ) * ((m : ℚ) - 3) / 2

@[simp] lemma rho_two : rho 2 = -1 := by norm_num [rho]

@[simp] lemma rho_three : rho 3 = 0 := by norm_num [rho]

/-- Support composition: every block at least 2 (Draft §2, Lemma 1). -/
def Supp (c : List ℕ) : Prop := ∀ m ∈ c, 2 ≤ m

instance : DecidablePred Supp := fun c => List.decidableBAll _ c

/-- Last part of a composition (junk value 0 on the empty list). -/
def lastPart : List ℕ → ℕ
  | [] => 0
  | [m] => m
  | _ :: l => lastPart l

@[simp] lemma lastPart_nil : lastPart [] = 0 := rfl

@[simp] lemma lastPart_singleton (m : ℕ) : lastPart [m] = m := rfl

lemma lastPart_cons_of_ne (a : ℕ) (l : List ℕ) (h : l ≠ []) :
    lastPart (a :: l) = lastPart l := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t => rfl

lemma lastPart_append_cons_of_ne (l₁ l₂ : List ℕ) (m : ℕ) (h : l₂ ≠ []) :
    lastPart (l₁ ++ m :: l₂) = lastPart l₂ := by
  induction l₁ with
  | nil =>
    simpa using lastPart_cons_of_ne m l₂ h
  | cons a l ih =>
    have hne : l ++ m :: l₂ ≠ [] := by simp
    simpa [lastPart_cons_of_ne a _ hne] using ih

lemma lastPart_append_cons_nil (l₁ : List ℕ) (m : ℕ) :
    lastPart (l₁ ++ [m]) = m := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    have hne : l ++ [m] ≠ [] := by simp
    simpa [lastPart_cons_of_ne a _ hne] using ih

lemma lastPart_mem (c : List ℕ) (h : c ≠ []) : lastPart c ∈ c := by
  induction c with
  | nil => exact absurd rfl h
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b t =>
      rw [lastPart_cons_of_ne a _ (by simp)]
      exact List.mem_cons_of_mem a (ih (by simp))

/-- `(m:ℚ) − 1`, as a named function (avoids list-coercion ambiguity). -/
def partQ (m : ℕ) : ℚ := (m : ℚ) - 1

/-- `(m! : ℚ)`, as a named function. -/
def factQ (m : ℕ) : ℚ := (Nat.factorial m : ℚ)

/-- The per-block factor `(m−1)/m!` of `G`. -/
def blockTerm (m : ℕ) : ℚ := partQ m / factQ m

/-- `Π_i (c_i − 1)/c_i!`. -/
def gprod (c : List ℕ) : ℚ := (c.map blockTerm).prod

/-- `G(c) = (Σc − 1)! · last(c) · Π_i (c_i−1)/c_i!` (Draft Definition 3). -/
def G (c : List ℕ) : ℚ :=
  (Nat.factorial (c.sum - 1) : ℚ) * (lastPart c : ℚ) * gprod c

/-- Cheng–Lin's `U_J` (Draft §1), in composition coordinates. -/
def U (c : List ℕ) : ℚ :=
  (lastPart c : ℚ) * (Nat.factorial (c.sum - 1) : ℚ) / (c.map factQ).prod

/-- Cheng–Lin's `a_J` (Draft §1): `Π(c_i−1) · Σ c_i(c_i−3)/2`. -/
def acoef (c : List ℕ) : ℚ := (c.map partQ).prod * (c.map rho).sum

/-- The weight `w(c) = G(c) · Σ_i ρ(c_i)` (Draft (W)). -/
def w (c : List ℕ) : ℚ := G c * (c.map rho).sum

/-! ### Elementary facts -/

lemma factorial_cast_ne_zero (m : ℕ) : (Nat.factorial m : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

lemma factorial_cast_pos (m : ℕ) : (0 : ℚ) < (Nat.factorial m : ℚ) := by
  exact_mod_cast Nat.factorial_pos m

lemma factprod_ne_zero (c : List ℕ) : (c.map factQ).prod ≠ 0 := by
  induction c with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_ne_zero (by simpa [factQ] using factorial_cast_ne_zero a) ih

@[simp] lemma gprod_nil : gprod [] = 1 := rfl

@[simp] lemma gprod_append (l₁ l₂ : List ℕ) :
    gprod (l₁ ++ l₂) = gprod l₁ * gprod l₂ := by
  simp [gprod]

@[simp] lemma gprod_cons (a : ℕ) (l : List ℕ) :
    gprod (a :: l) = blockTerm a * gprod l := by
  simp [gprod]

/-- `gprod` splits into the two product formulas (fidelity glue). -/
lemma gprod_eq_div (c : List ℕ) :
    gprod c = (c.map partQ).prod / (c.map factQ).prod := by
  induction c with
  | nil => simp [gprod]
  | cons a l ih =>
    rw [gprod_cons, ih, blockTerm]
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    rw [div_mul_div_comm]

/-- Fidelity: our `w` is Cheng–Lin's `U_J · a_J` (Draft (W) vs §1). -/
theorem w_eq_U_mul_a (c : List ℕ) : w c = U c * acoef c := by
  unfold w U acoef G
  rw [gprod_eq_div]
  have h := factprod_ne_zero c
  field_simp
  try ring

lemma blockTerm_pos (m : ℕ) (hm : 2 ≤ m) : 0 < blockTerm m := by
  unfold blockTerm partQ factQ
  apply div_pos
  · have : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    linarith
  · exact factorial_cast_pos m

lemma gprod_pos (c : List ℕ) (h : Supp c) : 0 < gprod c := by
  induction c with
  | nil => simp [gprod]
  | cons a l ih =>
    rw [gprod_cons]
    have ha : 2 ≤ a := h a List.mem_cons_self
    have hl : Supp l := fun m hm => h m (List.mem_cons_of_mem a hm)
    exact mul_pos (blockTerm_pos a ha) (ih hl)

/-- Positivity of `G` on nonempty support compositions (Draft Definition 3). -/
theorem G_pos (c : List ℕ) (hs : Supp c) (hne : c ≠ []) : 0 < G c := by
  unfold G
  have hlast : 2 ≤ lastPart c := hs _ (lastPart_mem c hne)
  have h1 : (0 : ℚ) < (Nat.factorial (c.sum - 1) : ℚ) := factorial_cast_pos _
  have h2 : (0 : ℚ) < (lastPart c : ℚ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hlast
  exact mul_pos (mul_pos h1 h2) (gprod_pos c hs)

lemma G_nonneg (c : List ℕ) (hs : Supp c) : 0 ≤ G c := by
  rcases eq_or_ne c [] with rfl | hne
  · simp [G, gprod]
  · exact le_of_lt (G_pos c hs hne)

/-- If some part equals 1 then `G` (hence `w`) vanishes (Draft Lemma 1). -/
lemma G_eq_zero_of_one_mem (c : List ℕ) (h : 1 ∈ c) : G c = 0 := by
  unfold G gprod
  have hb : blockTerm 1 = 0 := by norm_num [blockTerm, partQ, factQ]
  have hz : (0 : ℚ) ∈ c.map blockTerm := by
    rw [List.mem_map]; exact ⟨1, h, hb⟩
  rw [List.prod_eq_zero hz]
  ring

lemma w_eq_zero_of_one_mem (c : List ℕ) (h : 1 ∈ c) : w c = 0 := by
  unfold w
  rw [G_eq_zero_of_one_mem c h]
  ring

/-! ### List helpers (positional decomposition) -/

lemma getD_append_right' (l₁ l₂ : List ℕ) (k : ℕ) :
    (l₁ ++ l₂).getD (l₁.length + k) 0 = l₂.getD k 0 := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simpa [Nat.succ_add] using ih

lemma getD_append_length (l₁ l₂ : List ℕ) (m : ℕ) :
    (l₁ ++ m :: l₂).getD l₁.length 0 = m := by
  have h := getD_append_right' l₁ (m :: l₂) 0
  simp only [Nat.add_zero] at h
  rw [h]
  rfl

lemma getD_append_length_succ (l₁ l₂ : List ℕ) (m k : ℕ) :
    (l₁ ++ m :: l₂).getD (l₁.length + 1 + k) 0 = l₂.getD k 0 := by
  have h : l₁.length + 1 + k = l₁.length + (1 + k) := by omega
  rw [h, getD_append_right' l₁ (m :: l₂) (1 + k)]
  have h2 : 1 + k = k + 1 := by omega
  rw [h2]
  rfl

lemma length_take_of_lt (c : List ℕ) (i : ℕ) (hi : i ≤ c.length) :
    (c.take i).length = i := by
  simp [List.length_take]
  omega

/-- Decompose a list at a valid index `i`: `c = take i ++ c[i] :: drop (i+1)`. -/
lemma decomp_at (c : List ℕ) (i : ℕ) (hi : i < c.length) :
    c = c.take i ++ c.getD i 0 :: c.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i c]
  congr 1
  rw [List.getD_eq_getElem c 0 hi]
  exact List.drop_eq_getElem_cons hi

/-- Two-step decomposition at `i` with `i+1 < length`. -/
lemma decomp_at2 (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    c = c.take i ++ c.getD i 0 :: c.getD (i + 1) 0 :: c.drop (i + 2) := by
  have h1 : i < c.length := Nat.lt_of_succ_lt hi
  have d2 : c.drop (i + 1) = c.getD (i + 1) 0 :: c.drop (i + 2) := by
    rw [List.getD_eq_getElem c 0 hi]
    exact List.drop_eq_getElem_cons hi
  conv_lhs => rw [decomp_at c i h1, d2]

lemma sum_decomp (l₁ l₂ : List ℕ) (m : ℕ) :
    (l₁ ++ m :: l₂).sum = l₁.sum + m + l₂.sum := by
  simp [List.sum_append]
  ring

end ChowCone
