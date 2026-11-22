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

/-- Every pair with nonzero flow is a Boolean cover between two support
compositions: it splits a block as `n ↦ (p, n-p)` with both parts at least 2
and `min(p, n-p) ≤ 3`. -/
theorem fEdge4_ne_zero_cover (d : ℕ) (q c : Composition (d + 2)) (h : fEdge4 d q c ≠ 0) :
    ∃ i p, i < q.blocks.length ∧ 2 ≤ p ∧ 2 ≤ q.blocks.getD i 0 - p ∧
      splitAt q.blocks i p = c.blocks ∧ (p ≤ 3 ∨ q.blocks.getD i 0 - p ≤ 3) := by
  obtain ⟨i, p, h1, -, -, h4, h5⟩ := fEdgeOf_ne_zero_cover _ q c h
  obtain ⟨-, h6, h7⟩ := fdAll_ne_zero_suppEdge d q.blocks i p q.blocks_sum h5
  exact ⟨i, p, h1, h6, h7, h4, fdAll_used_edge d q.blocks i p q.blocks_sum h5⟩

/-- **No edge carrying flow meets a composition off the support.**  The
vertex type `Composition (d + 2)` also contains compositions with a part
equal to 1, among them those with final part 1, which are not flag types; a
pair with nonzero flow consists of two support compositions. -/
theorem fEdge4_ne_zero_supp (d : ℕ) (q c : Composition (d + 2)) (h : fEdge4 d q c ≠ 0) :
    Supp q.blocks ∧ Supp c.blocks := by
  obtain ⟨i, p, -, -, -, hsp, hne⟩ := fEdgeOf_ne_zero_cover _ q c h
  have := fdAll_ne_zero_supp d q.blocks i p q.blocks_sum hne
  rw [hsp] at this
  exact this

/-- **Identity (39), general form.**  For every `d ≥ 1` and any
`N U : Composition (d+2) → ℚ`, the sum `Σ (w^{(4)}/U) · N` equals the
combination of the differences `N_v/U_v - N_u/U_u` along the flow.  No
hypothesis on `N` or `U` is needed. -/
theorem fourth_moment_identity (d : ℕ) (hd : 1 ≤ d) (N U : Composition (d + 2) → ℚ) :
    ∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v
      = ∑ v : Composition (d + 2), ∑ u : Composition (d + 2),
          fEdge4 d v u * (N v / U v - N u / U u) := by
  rw [← flow_identity (fEdge4 d) (fun v => w4d d v.blocks) (fun v => N v / U v)
    (fEdge4_div d hd)]
  refine sum_congr rfl fun v _ => ?_
  ring

/-- **Fourth-moment certificate.**  For every `d ≥ 1` and `N = d + 2`: for
any `N U : Composition (d+2) → ℚ` that satisfy the monotonicity inequalities
along the edges carrying flow (supplied for flag numbers by Cheng and Lin's
Lemma 3.29, the external hypothesis), the sum `Σ (w^{(4)}/U) · N` equals the
nonnegative combination of monotonicity differences (identity (39)) and is
at most zero. -/
theorem fourth_moment_certificate (d : ℕ) (hd : 1 ≤ d)
    (N U : Composition (d + 2) → ℚ)
    (hmono : ∀ q c : Composition (d + 2), fEdge4 d q c ≠ 0 → N q / U q ≤ N c / U c) :
    (∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v
      = ∑ v : Composition (d + 2), ∑ u : Composition (d + 2),
          fEdge4 d v u * (N v / U v - N u / U u))
    ∧ ∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v ≤ 0 := by
  refine ⟨fourth_moment_identity d hd N U, ?_⟩
  have h := flow_nonneg_combination (fEdge4 d) (fun v => w4d d v.blocks)
    (fun v => N v / U v) (fEdge4_div d hd) (fun u v => fEdge4_nonneg d u v) hmono
  have he : ∑ v : Composition (d + 2), (w4d d v.blocks / U v) * N v
      = ∑ v : Composition (d + 2), w4d d v.blocks * (N v / U v) :=
    sum_congr rfl fun v _ => by ring
  rw [he]
  exact h

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

lemma U_comp_ne_zero (d : ℕ) (v : Composition (d + 2)) : U v.blocks ≠ 0 :=
  U_ne_zero v.blocks (fun _ hm => v.blocks_pos hm) (comp_blocks_ne_nil d v)

/-- **The coefficient form.**  With `U` the Boolean flag number
`U_J = (d+1)! n_r / Π n_i!` and `a^{(4)}` the coefficient (20): if
`N_J / U_J` is monotone along the edges carrying flow, then
`Σ_J a_J^{(4)} N_J ≤ 0`.  The sum runs over all compositions of `d + 2`;
`fourth_moment_coefficient_sum_nonpos_on_support` restricts it to the
support. -/
theorem fourth_moment_coefficient_sum_nonpos (d : ℕ) (hd : 1 ≤ d)
    (N : Composition (d + 2) → ℚ)
    (hmono : ∀ q c : Composition (d + 2), fEdge4 d q c ≠ 0 →
      N q / U q.blocks ≤ N c / U c.blocks) :
    ∑ v : Composition (d + 2), a4d d v.blocks * N v ≤ 0 := by
  have h := (fourth_moment_certificate d hd N (fun v => U v.blocks) hmono).2
  have he : ∀ v : Composition (d + 2),
      a4d d v.blocks * N v = (w4d d v.blocks / U v.blocks) * N v := by
    intro v
    rw [w4d_eq_U_mul_a4d, mul_div_cancel_left₀ _ (U_comp_ne_zero d v)]
  rw [sum_congr rfl fun v _ => he v]
  exact h

/-! ### The statement on the lattice of the manuscript

The manuscript's sums run over the subsets `J ⊆ [d]`, that is over the
compositions of `d + 2` with final part at least 2, and its coefficients
vanish off the support.  `Composition (d + 2)` has `2^(d+1)` elements, twice
as many.  The theorems below restrict both sums of (39) to the support
compositions, where every term of the manuscript's sums lives, and assume
monotonicity only between support compositions joined by an edge carrying
flow: instances of Cheng and Lin's Lemma 3.29 for `J ⊆ J' ⊆ [d]`.  They were
first proved in a probe of the review of release `v1.1`
(`RELEASE_CHECKS.md`). -/

/-- A support composition of `d + 2` has final part at least 2: it is the
flag type `c(J)` of a subset `J ⊆ [d]`. -/
theorem lastPart_ge_two_of_supp (d : ℕ) (c : Composition (d + 2)) (h : Supp c.blocks) :
    2 ≤ lastPart c.blocks :=
  h _ (lastPart_mem c.blocks (comp_blocks_ne_nil d c))

/-- The coefficient `a^{(4)}` vanishes off the support. -/
lemma a4d_eq_zero_of_not_supp (d : ℕ) (c : List ℕ) (h1 : ∀ m ∈ c, 1 ≤ m) (hs : ¬ Supp c) :
    a4d d c = 0 := by
  unfold a4d
  have hone := one_mem_of_not_supp c h1 hs
  have hz : (0 : ℚ) ∈ c.map partQ := by
    rw [List.mem_map]
    exact ⟨1, hone, by norm_num [partQ]⟩
  rw [List.prod_eq_zero hz, zero_mul]

/-- The support compositions of `d + 2`. -/
abbrev suppComps (d : ℕ) : Finset (Composition (d + 2)) :=
  univ.filter fun v : Composition (d + 2) => Supp v.blocks

lemma sum_a4d_suppComps (d : ℕ) (N : Composition (d + 2) → ℚ) :
    ∑ v ∈ suppComps d, a4d d v.blocks * N v
      = ∑ v : Composition (d + 2), a4d d v.blocks * N v := by
  refine sum_subset (filter_subset _ _) fun v _ hv => ?_
  have hns : ¬ Supp v.blocks := fun hs => hv (mem_filter.2 ⟨mem_univ v, hs⟩)
  rw [a4d_eq_zero_of_not_supp d v.blocks (fun m hm => v.blocks_pos hm) hns, zero_mul]

lemma fEdge4_eq_zero_left (d : ℕ) (v u : Composition (d + 2)) (h : ¬ Supp v.blocks) :
    fEdge4 d v u = 0 := by
  by_contra hne
  exact h (fEdge4_ne_zero_supp d v u hne).1

lemma fEdge4_eq_zero_right (d : ℕ) (v u : Composition (d + 2)) (h : ¬ Supp u.blocks) :
    fEdge4 d v u = 0 := by
  by_contra hne
  exact h (fEdge4_ne_zero_supp d v u hne).2

/-- **Identity (39).**  With the coefficient `a^{(4)}` and the Boolean flag
numbers `U`, both sums running over the support compositions: for every
`d ≥ 1` and every `N`,
`Σ_J a_J^{(4)} N_J = Σ f(J,J') (N_J/U_J - N_{J'}/U_{J'})`.  The values of `N`
off the support do not occur. -/
theorem fourth_moment_identity_on_support (d : ℕ) (hd : 1 ≤ d)
    (N : Composition (d + 2) → ℚ) :
    ∑ v ∈ suppComps d, a4d d v.blocks * N v
      = ∑ v ∈ suppComps d, ∑ u ∈ suppComps d,
          fEdge4 d v u * (N v / U v.blocks - N u / U u.blocks) := by
  have hid := fourth_moment_identity d hd N (fun v => U v.blocks)
  have hL : ∑ v : Composition (d + 2), (w4d d v.blocks / U v.blocks) * N v
      = ∑ v : Composition (d + 2), a4d d v.blocks * N v :=
    sum_congr rfl fun v _ => by
      rw [w4d_eq_U_mul_a4d, mul_div_cancel_left₀ _ (U_comp_ne_zero d v)]
  have hR : (∑ v ∈ suppComps d, ∑ u ∈ suppComps d,
        fEdge4 d v u * (N v / U v.blocks - N u / U u.blocks))
      = ∑ v : Composition (d + 2), ∑ u : Composition (d + 2),
          fEdge4 d v u * (N v / U v.blocks - N u / U u.blocks) := by
    have h1 : ∀ v ∈ suppComps d,
        (∑ u ∈ suppComps d, fEdge4 d v u * (N v / U v.blocks - N u / U u.blocks))
          = ∑ u : Composition (d + 2),
              fEdge4 d v u * (N v / U v.blocks - N u / U u.blocks) := by
      intro v _
      refine sum_subset (filter_subset _ _) fun u _ hu => ?_
      have hns : ¬ Supp u.blocks := fun hs => hu (mem_filter.2 ⟨mem_univ u, hs⟩)
      rw [fEdge4_eq_zero_right d v u hns, zero_mul]
    rw [sum_congr rfl h1]
    refine sum_subset (filter_subset _ _) fun v _ hv => ?_
    have hns : ¬ Supp v.blocks := fun hs => hv (mem_filter.2 ⟨mem_univ v, hs⟩)
    exact sum_eq_zero fun u _ => by rw [fEdge4_eq_zero_left d v u hns, zero_mul]
  rw [sum_a4d_suppComps, hR, ← hL]
  exact hid

/-- **The sign of (39).**  If `N_J / U_J` is monotone along the edges that
carry flow between support compositions, then `Σ_J a_J^{(4)} N_J ≤ 0`, the
sum running over the support compositions. -/
theorem fourth_moment_coefficient_sum_nonpos_on_support (d : ℕ) (hd : 1 ≤ d)
    (N : Composition (d + 2) → ℚ)
    (hmono : ∀ q c : Composition (d + 2), Supp q.blocks → Supp c.blocks →
      fEdge4 d q c ≠ 0 → N q / U q.blocks ≤ N c / U c.blocks) :
    ∑ v ∈ suppComps d, a4d d v.blocks * N v ≤ 0 := by
  rw [sum_a4d_suppComps]
  exact fourth_moment_coefficient_sum_nonpos d hd N fun q c hne =>
    hmono q c (fEdge4_ne_zero_supp d q c hne).1 (fEdge4_ne_zero_supp d q c hne).2 hne

end K4
end ChowCone
