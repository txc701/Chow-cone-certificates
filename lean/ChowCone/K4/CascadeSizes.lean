/-
Sizes of the cascade charges (rows 4–6 of Table 1) and the bounds of
Lemma 8.1.

Manuscript of 21 November 2026: Lemma 8.1, equations (36)–(38), and the
column "normalized amount" of rows 4–6 of Table 1.  The raw debit of a
final-right source is `R = 48 G(B)` with `B = P.(t,4)` (Section 7).  It is
normalized by `G` of the child of the charged occurrence.

Scope.  This file computes the normalized amount `48 r_j` charged by the
`j`-th origin and proves `Σ r_j ≤ 25/16`, and `Σ r_j ≤ 79/65` for `y = 3`.
It takes the raw debit `48 G(B)` from the text of Section 7; it does not
define the flows `f_0`, `f_d` or prove any statement about divergence or
about rows 1–3.
-/
import ChowCone.K4.CascadeOrigins
import ChowCone.Ratios

namespace ChowCone
namespace K4

open Finset

/-! ### The numbers `r_j` -/

/-- `r_j = 2^j ρ₀(y+2j)/ρ₀(y)` with `ρ₀(n) = (n-1)/n!`, equation (36).
`ρ₀` is `blockTerm` of `ChowCone.Basic`. -/
def r (y j : ℕ) : ℚ := 2 ^ j * blockTerm (y + 2 * j) / blockTerm y

lemma blockTerm_ne_zero (m : ℕ) (hm : 2 ≤ m) : blockTerm m ≠ 0 :=
  (blockTerm_pos m hm).ne'

lemma blockTerm_four : blockTerm 4 = 1 / 8 := by
  norm_num [blockTerm, partQ, factQ, Nat.factorial]

/-- `ρ₀(n+2)/ρ₀(n) = 1/((n+2)(n-1))`. -/
lemma blockTerm_add_two (n : ℕ) (hn : 2 ≤ n) :
    blockTerm (n + 2) = blockTerm n / (((n : ℚ) + 2) * ((n : ℚ) - 1)) := by
  have hf : Nat.factorial (n + 2) = (n + 2) * ((n + 1) * Nat.factorial n) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  unfold blockTerm partQ factQ
  rw [hf]
  push_cast
  have h0 : (Nat.factorial n : ℚ) ≠ 0 := factorial_cast_ne_zero n
  have h1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have h2 : (n : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem r_zero (y : ℕ) (hy : 2 ≤ y) : r y 0 = 1 := by
  unfold r
  simp [blockTerm_ne_zero y hy]

theorem r_pos (y j : ℕ) (hy : 2 ≤ y) : 0 < r y j := by
  unfold r
  have h1 := blockTerm_pos (y + 2 * j) (by omega)
  have h2 := blockTerm_pos y hy
  positivity

/-- The ratio formula of (37). -/
theorem r_succ (y j : ℕ) (hy : 2 ≤ y) :
    r y (j + 1) =
      r y j * (2 / (((y : ℚ) + 2 * j + 2) * ((y : ℚ) + 2 * j - 1))) := by
  unfold r
  have e : y + 2 * (j + 1) = (y + 2 * j) + 2 := by ring
  rw [e, blockTerm_add_two (y + 2 * j) (by omega)]
  have h0 := blockTerm_ne_zero y hy
  have h1 : (y : ℚ) + 2 * j - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ y := by exact_mod_cast hy
    have : (0 : ℚ) ≤ j := by positivity
    linarith
  have h2 : (y : ℚ) + 2 * j + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- One step of the ratio is at most `q` as soon as
`2 ≤ q (y+2j+2)(y+2j-1)`. -/
lemma r_succ_le (y j : ℕ) (hy : 2 ≤ y) (q : ℚ)
    (hq : 2 ≤ q * (((y : ℚ) + 2 * j + 2) * ((y : ℚ) + 2 * j - 1))) :
    r y (j + 1) ≤ q * r y j := by
  rw [r_succ y j hy, mul_comm q]
  have hy' : (2 : ℚ) ≤ y := by exact_mod_cast hy
  have hj : (0 : ℚ) ≤ j := by positivity
  have hD : 0 < ((y : ℚ) + 2 * j + 2) * ((y : ℚ) + 2 * j - 1) := by
    apply mul_pos <;> linarith
  apply mul_le_mul_of_nonneg_left _ (r_pos y j hy).le
  rw [div_le_iff₀ hD]
  exact hq

/-! ### A geometric bound -/

lemma geom_sum_le (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ range n, q ^ k ≤ 1 / (1 - q) := by
  have h : ∀ n : ℕ, (∑ k ∈ range n, q ^ k) * (1 - q) = 1 - q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, add_mul, ih]; ring
  have hpos : 0 < 1 - q := by linarith
  rw [le_div_iff₀ hpos, h n]
  have : 0 ≤ q ^ n := pow_nonneg hq0 n
  linarith

/-- If `u 0 = 1`, `u 1 ≤ a` and `u (j+2) ≤ q u (j+1)` with `0 ≤ q < 1`,
then every partial sum of `u` is at most `1 + a/(1-q)`. -/
lemma sum_le_of_ratio (u : ℕ → ℚ) (a q : ℚ) (h0 : u 0 = 1) (h1 : u 1 ≤ a)
    (hstep : ∀ j, u (j + 2) ≤ q * u (j + 1)) (hq0 : 0 ≤ q) (hq1 : q < 1) (ha : 0 ≤ a)
    (h : ℕ) : ∑ j ∈ range (h + 1), u j ≤ 1 + a / (1 - q) := by
  have hb : ∀ j, u (j + 1) ≤ a * q ^ j := by
    intro j
    induction j with
    | zero => simpa using h1
    | succ j ih =>
      calc u (j + 2) ≤ q * u (j + 1) := hstep j
        _ ≤ q * (a * q ^ j) := mul_le_mul_of_nonneg_left ih hq0
        _ = a * q ^ (j + 1) := by ring
  rw [sum_range_succ', h0]
  have h2 : ∑ j ∈ range h, u (j + 1) ≤ ∑ j ∈ range h, a * q ^ j :=
    sum_le_sum fun j _ => hb j
  have h3 : ∑ j ∈ range h, a * q ^ j = a * ∑ j ∈ range h, q ^ j := by
    rw [mul_sum]
  have h4 := mul_le_mul_of_nonneg_left (geom_sum_le q hq0 hq1 h) ha
  have h5 : a * (1 / (1 - q)) = a / (1 - q) := by ring
  linarith

/-- The bound of (37): `Σ_{j ≤ h} r_j ≤ 25/16` for every `y ≥ 2`. -/
theorem sum_r_le (y h : ℕ) (hy : 2 ≤ y) : ∑ j ∈ range (h + 1), r y j ≤ 25 / 16 := by
  have hy' : (2 : ℚ) ≤ y := by exact_mod_cast hy
  have h1 : r y 1 ≤ 1 / 2 := by
    have := r_succ_le y 0 hy (1 / 2) (by push_cast; nlinarith)
    rwa [r_zero y hy, mul_one] at this
  have hstep : ∀ j, r y (j + 2) ≤ 1 / 9 * r y (j + 1) := by
    intro j
    have hj : (0 : ℚ) ≤ j := by positivity
    exact r_succ_le y (j + 1) hy (1 / 9) (by push_cast; nlinarith)
  have := sum_le_of_ratio (r y) (1 / 2) (1 / 9) (r_zero y hy) h1 hstep
    (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢
  linarith

/-- The bound (38) for a terminal `F_3` edge: `y = 3` and
`Σ_{j ≤ h} r_j ≤ 79/65 < 5/4`. -/
theorem sum_r_three_le (h : ℕ) : ∑ j ∈ range (h + 1), r 3 j ≤ 79 / 65 := by
  have h1 : r 3 1 ≤ 1 / 5 := by
    have := r_succ_le 3 0 (by norm_num) (1 / 5) (by push_cast; norm_num)
    rwa [r_zero 3 (by norm_num), mul_one] at this
  have hstep : ∀ j, r 3 (j + 2) ≤ 1 / 14 * r 3 (j + 1) := by
    intro j
    have hj : (0 : ℚ) ≤ j := by positivity
    exact r_succ_le 3 (j + 1) (by norm_num) (1 / 14) (by push_cast; nlinarith)
  have := sum_le_of_ratio (r 3) (1 / 5) (1 / 14) (r_zero 3 (by norm_num)) h1 hstep
    (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this ⊢
  linarith

/-! ### The normalized amount charged by an origin -/

lemma gprod_replicate_two (j : ℕ) : gprod (List.replicate j 2) = (1 / 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.replicate_succ, gprod_cons, ih, blockTerm_two]; ring

lemma lastPart_append_pair (l : List ℕ) (a b : ℕ) : lastPart (l ++ [a, b]) = b := by
  rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp, lastPart_append_cons_nil]

/-- `Y` and `Z` have the same blocks in a different order and the same
final block. -/
theorem G_sqY_eq_sqZ (Q : List ℕ) (y : ℕ) : G (sqY Q y) = G (sqZ Q y) := by
  unfold G sqY sqZ
  have hs : (Q ++ [y, 2, 2]).sum = (Q ++ [2, y, 2]).sum := by
    simp [List.sum_append]; omega
  have hl1 : lastPart (Q ++ [y, 2, 2]) = 2 := by
    rw [show Q ++ [y, 2, 2] = (Q ++ [y]) ++ [2, 2] by simp, lastPart_append_pair]
  have hl2 : lastPart (Q ++ [2, y, 2]) = 2 := by
    rw [show Q ++ [2, y, 2] = (Q ++ [2]) ++ [y, 2] by simp, lastPart_append_pair]
  rw [hs, hl1, hl2]
  simp only [gprod_append, gprod_cons, gprod_nil]
  ring

/-- Cancellation of the unaffected factors of `G`:
`G(P.(y+2j,4)) = r_j · G(P.2^j.(2,y,2))`. -/
theorem G_source_child_eq (P : List ℕ) (y j : ℕ) (hy : 2 ≤ y) :
    G (P ++ [y + 2 * j, 4]) = r y j * G (sqZ (P ++ List.replicate j 2) y) := by
  unfold G sqZ r
  have hs : (P ++ List.replicate j 2 ++ [2, y, 2]).sum = (P ++ [y + 2 * j, 4]).sum := by
    simp [List.sum_append, List.sum_replicate]; ring
  have hl1 : lastPart (P ++ [y + 2 * j, 4]) = 4 := lastPart_append_pair _ _ _
  have hl2 : lastPart (P ++ List.replicate j 2 ++ [2, y, 2]) = 2 := by
    rw [show P ++ List.replicate j 2 ++ [2, y, 2]
      = (P ++ List.replicate j 2 ++ [2]) ++ [y, 2] by simp, lastPart_append_pair]
  rw [hs, hl1, hl2]
  simp only [gprod_append, gprod_cons, gprod_nil, gprod_replicate_two, blockTerm_two,
    blockTerm_four]
  have h0 := blockTerm_ne_zero y hy
  have h2 : (2 : ℚ) ^ j * (1 / 2) ^ j = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  push_cast
  linear_combination (-(16 : ℚ) * gprod P * blockTerm (y + 2 * j)) * h2

/-- The raw debit `R = 48 G(B)` left by the final-right square of a source,
`B = P.(t,4)` (Section 7). -/
def Source.rawDebit (s : Source) : ℚ := 48 * G s.occ.child

/-- **Normalized amount, rows 4–6.**  The `j`-th origin of the label at
`Q.(y+2,2)` charges `48 r_j` times `G` of the child of the charged
occurrence. -/
theorem rawDebit_origin (Q : List ℕ) (y j : ℕ) (hy : 2 ≤ y) (hj : j ≤ trailingTwos Q) :
    (origin Q y j).rawDebit = 48 * r y j * G (chargeAt Q y).label.child := by
  have hQ := (eq_append_replicate_iff Q _ j).2 ⟨hj, rfl⟩
  have hc : G (chargeAt Q y).label.child = G (sqZ Q y) := by
    rw [chargeAt_child Q y hy]
    split_ifs
    · rfl
    · exact G_sqY_eq_sqZ Q y
  unfold Source.rawDebit
  rw [Source.occ_child, hc]
  simp only [origin]
  rw [G_source_child_eq _ y j hy, ← hQ]
  ring

/-! ### Total charge on a label -/

/-- The total raw amount charged to the label at `Q.(y+2,2)` by all sources
at size `N`, with multiplicity, is `48 Σ_{j ≤ h} r_j` times `G` of the child
of the charged occurrence. -/
theorem total_charge (N : ℕ) (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y)
    (hN : Q.sum + y + 4 = N) :
    ∑ s ∈ (validSources_finite N).toFinset,
        (s.trace.count (chargeAt Q y) : ℚ) * s.rawDebit =
      48 * (∑ j ∈ range (trailingTwos Q + 1), r y j) * G (chargeAt Q y).label.child := by
  have himg : (origins Q y).toFinset = (range (trailingTwos Q + 1)).image (origin Q y) := by
    ext s
    simp [origins]
  have h1 : ∀ s ∈ (validSources_finite N).toFinset,
      (s.trace.count (chargeAt Q y) : ℚ) * s.rawDebit =
        if s ∈ (origins Q y).toFinset then s.rawDebit else 0 := by
    intro s _
    rw [count_trace_eq_count_origins s Q y hy]
    by_cases h : s ∈ origins Q y
    · rw [List.count_eq_one_of_mem (origins_nodup Q y) h, if_pos (List.mem_toFinset.2 h)]
      simp
    · rw [List.count_eq_zero_of_not_mem h, if_neg (by simpa using h)]
      simp
  have hsub : (validSources_finite N).toFinset ∩ (origins Q y).toFinset =
      (origins Q y).toFinset := by
    refine inter_eq_right.2 fun s hs => ?_
    obtain ⟨j, hj, rfl⟩ := mem_origins.1 (List.mem_toFinset.1 hs)
    exact (Set.Finite.mem_toFinset _).2 (origin_valid N Q y j hQ hy hN hj)
  rw [sum_congr rfl h1, sum_ite_mem, hsub, himg,
    sum_image (fun i _ j _ h => origin_injective Q y h), mul_assoc, mul_comm _ (G _),
    mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [rawDebit_origin Q y j hy (by have := mem_range.1 hj; omega)]
  ring

lemma chargeAt_child_supp (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y) :
    Supp (chargeAt Q y).label.child ∧ (chargeAt Q y).label.child ≠ [] := by
  rw [chargeAt_child Q y hy]
  split_ifs
  · exact ⟨supp_append.2 ⟨hQ, by intro m hm; simp at hm; omega⟩, by simp [sqZ]⟩
  · exact ⟨supp_append.2 ⟨hQ, by intro m hm; simp at hm; omega⟩, by simp [sqY]⟩

/-- All cascades together charge at most `75` normalized units to a label
of rows 4–6. -/
theorem total_charge_le (N : ℕ) (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y)
    (hN : Q.sum + y + 4 = N) :
    ∑ s ∈ (validSources_finite N).toFinset,
        (s.trace.count (chargeAt Q y) : ℚ) * s.rawDebit ≤
      75 * G (chargeAt Q y).label.child := by
  rw [total_charge N Q y hQ hy hN]
  have hG := (G_pos _ (chargeAt_child_supp Q y hQ hy).1 (chargeAt_child_supp Q y hQ hy).2).le
  have hs := sum_r_le y (trailingTwos Q) hy
  have : 48 * (∑ j ∈ range (trailingTwos Q + 1), r y j) ≤ 75 := by linarith
  exact mul_le_mul_of_nonneg_right this hG

/-- All cascades together charge strictly fewer than `60` normalized units
to a terminal `F_3` label (row 6). -/
theorem total_charge_F3_lt (N : ℕ) (Q : List ℕ) (hQ : Supp Q) (hN : Q.sum + 3 + 4 = N) :
    ∑ s ∈ (validSources_finite N).toFinset,
        (s.trace.count (chargeAt Q 3) : ℚ) * s.rawDebit <
      60 * G (chargeAt Q 3).label.child := by
  rw [total_charge N Q 3 hQ (by norm_num) hN]
  have hG := G_pos _ (chargeAt_child_supp Q 3 hQ (by norm_num)).1
    (chargeAt_child_supp Q 3 hQ (by norm_num)).2
  have hs := sum_r_three_le (trailingTwos Q)
  have : 48 * (∑ j ∈ range (trailingTwos Q + 1), r 3 j) < 60 := by linarith
  exact mul_lt_mul_of_pos_right this hG

/-! ### Diagnostic values -/

example : r 2 1 = 1 / 2 := by norm_num [r, blockTerm, partQ, factQ, Nat.factorial]

example : r 2 2 = 1 / 18 := by norm_num [r, blockTerm, partQ, factQ, Nat.factorial]

example : r 3 1 = 1 / 5 := by norm_num [r, blockTerm, partQ, factQ, Nat.factorial]

example : r 4 1 = 1 / 9 := by norm_num [r, blockTerm, partQ, factQ, Nat.factorial]

end K4
end ChowCone
