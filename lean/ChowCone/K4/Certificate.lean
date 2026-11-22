/-
The fourth-moment certificate on the Boolean lattice.

Manuscript of 21 November 2026: Lemma 3.1 (finite-poset flow lemma),
Section 9 after Theorem 9.1: extension of `f_d` by zero to the full Boolean
lattice, the identity (39)
`Σ_J a_J^{(4)} N_J = Σ f_d(J,J') (N_J/U_J - N_{J'}/U_{J'})`, and its sign
under Cheng and Lin's Lemma 3.29 (equation (8)).

Scope.  The vertices are the compositions of `N = d + 2` (Mathlib's
`Composition`), as in the `k = 2` file `ChowCone.Main`.  Cheng and Lin's
Lemma 3.29 enters as the hypothesis `hmono`; no matroid or Chow-ring theory
is formalized, and the passage from `Σ_J a_J^{(4)} N_J ≤ 0` to the
inequality of fourth moments (equation (19)) is not formalized.
-/
import ChowCone.K4.UniformFlow

namespace ChowCone
namespace K4

open Finset

variable {n : ℕ}

/-! ### A positional flow as a flow on vertex pairs -/

/-- Total flow on the cover edge from `q` to `c` (zero if `c` is not
obtained from `q` by one split): the sum of `f` over the splits realizing
it.  For `f = F` this is `fEdge` of `ChowCone.Main`. -/
def fEdgeOf (f : EdgeFlow) (q c : Composition n) : ℚ :=
  ∑ i ∈ range q.blocks.length, ∑ p ∈ Icc 1 (q.blocks.getD i 0 - 1),
    if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0

theorem fEdgeOf_F (q c : Composition n) : fEdgeOf F q c = fEdge q c := rfl

/-- Outflow collapse: each admissible split lands on exactly one
composition. -/
lemma sum_fEdgeOf_out (f : EdgeFlow) (q : Composition n) :
    ∑ c : Composition n, fEdgeOf f q c = outSumOf f q.blocks := by
  unfold fEdgeOf outSumOf
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  have hi' := mem_range.1 hi
  have hp' := mem_Icc.1 hp
  have hsum : (splitAt q.blocks i p).sum = n := by
    rw [splitAt_sum q.blocks i p hi' (by omega)]
    exact q.blocks_sum
  have hpos : ∀ x ∈ splitAt q.blocks i p, 0 < x := by
    intro x hx
    rcases splitAt_mem q.blocks i p x hx with h | h | h
    · exact q.blocks_pos h
    · omega
    · omega
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Composition n, c₀.blocks = splitAt q.blocks i p :=
    ⟨⟨splitAt q.blocks i p, fun {x} hx => hpos x hx, hsum⟩, rfl⟩
  have hiff : ∀ c : Composition n, (splitAt q.blocks i p = c.blocks) ↔ c = c₀ := by
    intro c
    constructor
    · intro h
      exact (Composition.ext (hc₀.trans h)).symm
    · rintro rfl
      exact hc₀.symm
  calc (∑ c : Composition n, if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0)
      = ∑ c : Composition n, if c = c₀ then f q.blocks i p else 0 := by
        refine sum_congr rfl fun c _ => ?_
        rw [if_congr (hiff c) rfl rfl]
    _ = f q.blocks i p := by
        rw [sum_ite_eq' univ c₀ (fun _ => f q.blocks i p)]
        exact if_pos (mem_univ c₀)

/-- For fixed `(i, p)`, at most one parent can split onto `c`, namely
`mergeAt c i` with `p = c_i`. -/
lemma sum_fEdgeOf_in_term (f : EdgeFlow) (c : Composition n) (i p : ℕ) :
    (∑ q : Composition n, if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0)
    = if i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
      then f (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0 := by
  by_cases hcase : i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
  · obtain ⟨hilen, rfl⟩ := hcase
    rw [if_pos ⟨hilen, rfl⟩]
    have hsumM : (mergeAt c.blocks i).sum = n := by
      rw [mergeAt_sum c.blocks i hilen]
      exact c.blocks_sum
    have hposM : ∀ x ∈ mergeAt c.blocks i, 0 < x := by
      intro x hx
      rw [mergeAt_def] at hx
      rcases List.mem_append.1 hx with h | h
      · exact c.blocks_pos (List.take_subset i c.blocks h)
      · rcases List.mem_cons.1 h with rfl | h
        · have h1 := c.blocks_pos (getD_mem c.blocks i (by omega))
          omega
        · exact c.blocks_pos (List.drop_subset (i + 2) c.blocks h)
    obtain ⟨qM, hqM⟩ : ∃ qM : Composition n, qM.blocks = mergeAt c.blocks i :=
      ⟨⟨mergeAt c.blocks i, fun {x} hx => hposM x hx, hsumM⟩, rfl⟩
    have hiff : ∀ q : Composition n,
        (splitAt q.blocks i (c.blocks.getD i 0) = c.blocks) ↔ q = qM := by
      intro q
      constructor
      · intro h
        have hvalid := splitAt_valid_of_pos q.blocks c.blocks i (c.blocks.getD i 0)
          (comp_blocks_pos c) h
        have hinv := splitAt_inversion q.blocks c.blocks i (c.blocks.getD i 0)
          hvalid.1 hvalid.2.1 hvalid.2.2 h
        exact Composition.ext (hinv.1.trans hqM.symm)
      · rintro rfl
        rw [hqM]
        exact splitAt_mergeAt c.blocks i hilen
    calc (∑ q : Composition n,
            if splitAt q.blocks i (c.blocks.getD i 0) = c.blocks
            then f q.blocks i (c.blocks.getD i 0) else 0)
        = ∑ q : Composition n,
            if q = qM then f (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0 := by
          refine sum_congr rfl fun q _ => ?_
          by_cases h : q = qM
          · rw [if_pos ((hiff q).mpr h), if_pos h, h, hqM]
          · rw [if_neg (fun hc => h ((hiff q).mp hc)), if_neg h]
      _ = f (mergeAt c.blocks i) i (c.blocks.getD i 0) := by
          rw [sum_ite_eq' univ qM (fun _ => f (mergeAt c.blocks i) i (c.blocks.getD i 0))]
          exact if_pos (mem_univ qM)
  · rw [if_neg hcase]
    refine sum_eq_zero fun q _ => ?_
    by_cases h : splitAt q.blocks i p = c.blocks
    · exfalso
      have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p (comp_blocks_pos c) h
      have hinv := splitAt_inversion q.blocks c.blocks i p hvalid.1 hvalid.2.1 hvalid.2.2 h
      exact hcase ⟨hinv.2.2, hinv.2.1.symm⟩
    · rw [if_neg h]

/-- Inflow collapse: every edge into `c` merges a unique adjacent pair of
blocks of `c`. -/
lemma sum_fEdgeOf_in (f : EdgeFlow) (c : Composition n) :
    ∑ q : Composition n, fEdgeOf f q c = inSumOf f c.blocks := by
  have hT : ∀ q : Composition n, fEdgeOf f q c
      = ∑ i ∈ range n, ∑ p ∈ range (n + 1),
          (if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0) := by
    intro q
    unfold fEdgeOf
    have step1 : ∀ i,
        (∑ p ∈ Icc 1 (q.blocks.getD i 0 - 1),
          if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0)
        = ∑ p ∈ range (n + 1),
            if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0 := by
      intro i
      apply sum_subset
      · intro p hp
        rw [mem_Icc] at hp
        rw [mem_range]
        have := comp_getD_le q i
        omega
      · intro p _ hp
        rw [if_neg]
        intro hsp
        have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p (comp_blocks_pos c) hsp
        exact hp (mem_Icc.2 ⟨hvalid.2.1, by have := hvalid.2.2; omega⟩)
    rw [sum_congr rfl (fun i _ => step1 i)]
    apply sum_subset
    · intro x hx
      exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) (comp_length_le q))
    · intro i _ hi
      refine sum_eq_zero fun p _ => ?_
      rw [if_neg]
      intro hsp
      have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p (comp_blocks_pos c) hsp
      exact hi (mem_range.2 hvalid.1)
  rw [sum_congr rfl (fun q _ => hT q)]
  rw [sum_comm]
  rw [sum_congr rfl (fun i _ => sum_comm (s := univ)
    (t := range (n + 1)) (f := fun (q : Composition n) (p : ℕ) =>
      if splitAt q.blocks i p = c.blocks then f q.blocks i p else 0))]
  rw [sum_congr rfl (fun i _ => sum_congr rfl (fun p _ => sum_fEdgeOf_in_term f c i p))]
  have hstep2 : ∀ i,
      (∑ p ∈ range (n + 1),
        if i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
        then f (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0)
      = (if i + 1 < c.blocks.length
         then f (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0) := by
    intro i
    by_cases hil : i + 1 < c.blocks.length
    · rw [if_pos hil]
      have : ∀ p, (i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0)
          ↔ p = c.blocks.getD i 0 := fun p => and_iff_right hil
      rw [sum_congr rfl (fun p _ => if_congr (this p) rfl rfl)]
      rw [sum_ite_eq' (range (n + 1)) (c.blocks.getD i 0)
        (fun _ => f (mergeAt c.blocks i) i (c.blocks.getD i 0))]
      rw [if_pos (mem_range.mpr (by
        have := comp_getD_le c i
        omega))]
    · rw [if_neg hil]
      refine sum_eq_zero fun p _ => ?_
      rw [if_neg (fun h => hil h.1)]
  rw [sum_congr rfl (fun i _ => hstep2 i)]
  unfold inSumOf
  symm
  have hgoal : ∀ i ∈ range (c.blocks.length - 1),
      f (mergeAt c.blocks i) i (c.blocks.getD i 0)
        = (if i + 1 < c.blocks.length
           then f (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0) := by
    intro i hi
    rw [if_pos (by
      have := mem_range.1 hi
      omega)]
  rw [sum_congr rfl hgoal]
  apply sum_subset
  · intro x hx
    refine mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) ?_)
    have := comp_length_le c
    omega
  · intro i _ hi
    rw [if_neg (by
      have hle : c.blocks.length - 1 ≤ i := by
        by_contra hlt
        exact hi (mem_range.mpr (by omega))
      omega)]

/-- The divergence on vertex pairs is the positional divergence. -/
theorem fEdgeOf_div (f : EdgeFlow) (v : Composition n) :
    (∑ u : Composition n, fEdgeOf f v u) - (∑ u : Composition n, fEdgeOf f u v)
      = divOf f v.blocks := by
  rw [sum_fEdgeOf_out, sum_fEdgeOf_in]
  rfl

lemma fEdgeOf_nonneg (f : EdgeFlow) (hf : ∀ (c : List ℕ) (i p : ℕ), c.sum = n → 0 ≤ f c i p)
    (q c : Composition n) : 0 ≤ fEdgeOf f q c := by
  refine sum_nonneg fun i _ => sum_nonneg fun p _ => ?_
  split_ifs
  · exact hf _ _ _ q.blocks_sum
  · exact le_refl 0

/-- A vertex pair with nonzero flow is a Boolean cover: `c` is obtained
from `q` by one legal split, and `f` is nonzero on that split. -/
lemma fEdgeOf_ne_zero_cover (f : EdgeFlow) (q c : Composition n) (h : fEdgeOf f q c ≠ 0) :
    ∃ i p, i < q.blocks.length ∧ 1 ≤ p ∧ p < q.blocks.getD i 0 ∧
      splitAt q.blocks i p = c.blocks ∧ f q.blocks i p ≠ 0 := by
  obtain ⟨i, _, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨p, _, hne2⟩ := exists_ne_zero_of_sum_ne_zero hne
  by_cases hsp : splitAt q.blocks i p = c.blocks
  · have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p (comp_blocks_pos c) hsp
    rw [if_pos hsp] at hne2
    exact ⟨i, p, hvalid.1, hvalid.2.1, hvalid.2.2, hsp, hne2⟩
  · rw [if_neg hsp] at hne2
    exact absurd rfl hne2

/-! ### The fourth-moment flow on the Boolean lattice -/

/-- The flow of Theorem 9.1 on the compositions of `N = d + 2`. -/
noncomputable def fEdge4 (d : ℕ) (q c : Composition (d + 2)) : ℚ := fEdgeOf (fdAll d) q c

theorem fEdge4_nonneg (d : ℕ) (q c : Composition (d + 2)) : 0 ≤ fEdge4 d q c :=
  fEdgeOf_nonneg _ (fun c i p hN => fdAll_nonneg d c i p hN) q c

/-- The divergence of the flow is `w^{(4)}` at every vertex of the Boolean
lattice, on and off the support. -/
theorem fEdge4_div (d : ℕ) (hd : 1 ≤ d) (v : Composition (d + 2)) :
    (∑ u : Composition (d + 2), fEdge4 d v u) - (∑ u : Composition (d + 2), fEdge4 d u v)
      = w4d d v.blocks := by
  unfold fEdge4
  rw [fEdgeOf_div]
  exact divOf_fdAll d hd v.blocks (fun m hm => v.blocks_pos hm) v.blocks_sum

/-- Every pair with nonzero flow is a Boolean cover that splits a block as
`n ↦ (p, n-p)` with `min(p, n-p) ≤ 3`. -/
theorem fEdge4_ne_zero_cover (d : ℕ) (q c : Composition (d + 2)) (h : fEdge4 d q c ≠ 0) :
    ∃ i p, i < q.blocks.length ∧ 1 ≤ p ∧ p < q.blocks.getD i 0 ∧
      splitAt q.blocks i p = c.blocks ∧ (p ≤ 3 ∨ q.blocks.getD i 0 - p ≤ 3) := by
  obtain ⟨i, p, h1, h2, h3, h4, h5⟩ := fEdgeOf_ne_zero_cover _ q c h
  exact ⟨i, p, h1, h2, h3, h4, fdAll_used_edge d q.blocks i p q.blocks_sum h5⟩

/-- **Fourth-moment certificate.**  For every `d ≥ 1` and `N = d + 2`: the
flow `fEdge4` on the compositions of `N` is nonnegative and has divergence
`w^{(4)}`.  Consequently, for any `N U : Composition (d+2) → ℚ` with
`U ≠ 0` that satisfy the monotonicity inequalities along the edges carrying
flow (supplied for flag numbers by Cheng and Lin's Lemma 3.29, the external
hypothesis), the sum `Σ (w^{(4)}/U) · N` equals the nonnegative combination
of monotonicity differences (identity (39)) and is at most zero. -/
theorem fourth_moment_certificate (d : ℕ) (hd : 1 ≤ d)
    (N U : Composition (d + 2) → ℚ) (hU : ∀ v, U v ≠ 0)
    (hmono : ∀ q c : Composition (d + 2), fEdge4 d q c ≠ 0 → N q / U q ≤ N c / U c) :
    (∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v
      = ∑ v : Composition (d + 2), ∑ u : Composition (d + 2),
          fEdge4 d v u * (N v / U v - N u / U u))
    ∧ ∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v ≤ 0 :=
  ⟨conjecture_combination (fEdge4 d) (fun v => w4d d v.blocks) N U (fEdge4_div d hd) hU,
   conjecture_nonpos (fEdge4 d) (fun v => w4d d v.blocks) N U (fEdge4_div d hd)
     (fun u v => fEdge4_nonneg d u v) hU hmono⟩

/-! ### The same statement with the Boolean flag numbers -/

lemma U_ne_zero (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (hne : c ≠ []) : U c ≠ 0 := by
  unfold U
  have hl : 1 ≤ lastPart c := h1 _ (lastPart_mem c hne)
  have h2 : (lastPart c : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact div_ne_zero (mul_ne_zero h2 (factorial_cast_ne_zero _)) (factprod_ne_zero c)

lemma comp_blocks_ne_nil (d : ℕ) (v : Composition (d + 2)) : v.blocks ≠ [] := by
  intro h
  have := v.blocks_sum
  rw [h] at this
  simp at this

/-- **The coefficient form.**  With `U` the Boolean flag number
`U_J = (d+1)! n_r / Π n_i!` and `a^{(4)}` the coefficient (20): if
`N_J / U_J` is monotone along the edges carrying flow, then
`Σ_J a_J^{(4)} N_J ≤ 0`. -/
theorem fourth_moment_coefficient_sum_nonpos (d : ℕ) (hd : 1 ≤ d)
    (N : Composition (d + 2) → ℚ)
    (hmono : ∀ q c : Composition (d + 2), fEdge4 d q c ≠ 0 →
      N q / U q.blocks ≤ N c / U c.blocks) :
    ∑ v : Composition (d + 2), a4d d v.blocks * N v ≤ 0 := by
  have hU : ∀ v : Composition (d + 2), U v.blocks ≠ 0 := fun v =>
    U_ne_zero v.blocks (fun m hm => v.blocks_pos hm) (comp_blocks_ne_nil d v)
  have h := (fourth_moment_certificate d hd N (fun v => U v.blocks) hU hmono).2
  have he : ∀ v : Composition (d + 2),
      a4d d v.blocks * N v = (w4d d v.blocks / U v.blocks) * N v := by
    intro v
    rw [w4d_eq_U_mul_a4d, mul_div_cancel_left₀ _ (hU v)]
  rw [sum_congr rfl fun v _ => he v]
  exact h

end K4
end ChowCone
