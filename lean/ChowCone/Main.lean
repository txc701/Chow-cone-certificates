/-
Assembly (Draft Theorem 1/1′): the explicit certificate as a vertex-pair
flow on the finite type `Composition n`, its divergence identity, and the
resulting nonnegative-combination statement with Cheng–Lin Lemma 3.29 as an
external hypothesis.
-/
import ChowCone.Divergence
import ChowCone.Abstract

namespace ChowCone

open Finset

/-! ### Structural helpers for splits as relations between compositions -/

lemma mem_le_sum {x : ℕ} {l : List ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [List.sum_cons]
    · have := ih h
      simp [List.sum_cons]
      omega

lemma splitAt_sum (c : List ℕ) (i p : ℕ) (hi : i < c.length)
    (hp : p ≤ c.getD i 0) : (splitAt c i p).sum = c.sum := by
  conv_rhs => rw [decomp_at c i hi]
  rw [splitAt_eq]
  simp only [List.sum_append, List.sum_cons]
  omega

lemma mergeAt_sum (c : List ℕ) (i : ℕ) (hi : i + 1 < c.length) :
    (mergeAt c i).sum = c.sum := by
  conv_rhs => rw [decomp_at2 c i hi]
  rw [mergeAt_def]
  simp only [List.sum_append, List.sum_cons]
  omega

lemma p_mem_splitAt (c : List ℕ) (i p : ℕ) : p ∈ splitAt c i p := by
  rw [splitAt_eq]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_self))

lemma rest_mem_splitAt (c : List ℕ) (i p : ℕ) :
    c.getD i 0 - p ∈ splitAt c i p := by
  rw [splitAt_eq]
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    List.mem_cons_self)))

lemma getD_eq_zero_of_le (c : List ℕ) (i : ℕ) (h : c.length ≤ i) :
    c.getD i 0 = 0 :=
  List.getD_eq_default c 0 h

/-- If a split of `q` produces a positive-parts list, the split data was
valid (Draft Lemma 7 aliasing/well-definedness: degenerate splits cannot
match a genuine composition). -/
lemma splitAt_valid_of_pos (q c : List ℕ) (i p : ℕ)
    (hcpos : ∀ x ∈ c, 1 ≤ x) (h : splitAt q i p = c) :
    i < q.length ∧ 1 ≤ p ∧ p < q.getD i 0 := by
  have hp : 1 ≤ p := hcpos p (h ▸ p_mem_splitAt q i p)
  have hrest : 1 ≤ q.getD i 0 - p := hcpos _ (h ▸ rest_mem_splitAt q i p)
  have hplt : p < q.getD i 0 := by omega
  have hi : i < q.length := by
    by_contra hle
    have := getD_eq_zero_of_le q i (by omega)
    omega
  exact ⟨hi, hp, hplt⟩

/-- Inversion (Draft Lemma 7, completeness of the reverse map): a valid
split of `q` landing on `c` forces `q = mergeAt c i` and offset `c_i`. -/
lemma splitAt_inversion (q c : List ℕ) (i p : ℕ)
    (hq : i < q.length) (hp1 : 1 ≤ p) (hplt : p < q.getD i 0)
    (h : splitAt q i p = c) :
    q = mergeAt c i ∧ c.getD i 0 = p ∧ i + 1 < c.length := by
  have hlen : (q.take i).length = i := length_take_of_lt q i (le_of_lt hq)
  have hc : c = q.take i ++ p :: (q.getD i 0 - p) :: q.drop (i + 1) := by
    rw [← h, splitAt_eq]
  -- the three coordinates of c
  have hci : c.getD i 0 = p := by
    rw [hc]
    have := getD_append_length (q.take i) ((q.getD i 0 - p) :: q.drop (i + 1)) p
    rwa [hlen] at this
  have hci1 : c.getD (i + 1) 0 = q.getD i 0 - p := by
    rw [hc]
    have := getD_append_length_succ (q.take i)
      ((q.getD i 0 - p) :: q.drop (i + 1)) p 0
    rw [hlen] at this
    simpa using this
  have hclen : i + 1 < c.length := by
    rw [hc, List.length_append, hlen]
    simp
  refine ⟨?_, hci, hclen⟩
  -- q = mergeAt c i by surgery
  have htake : c.take i = q.take i := by
    rw [hc]
    have := take_append_length (q.take i)
      (p :: (q.getD i 0 - p) :: q.drop (i + 1))
    rw [hlen] at this
    exact this
  have hdrop : c.drop (i + 2) = q.drop (i + 1) := by
    rw [hc]
    have h2 : (q.take i ++ p :: (q.getD i 0 - p) :: q.drop (i + 1))
        = (q.take i ++ [p]) ++ (q.getD i 0 - p) :: q.drop (i + 1) := by
      simp
    rw [h2]
    have := drop_append_length_succ (q.take i ++ [p]) (q.drop (i + 1))
      (q.getD i 0 - p)
    rw [List.length_append, hlen] at this
    simpa [show i + 1 + 1 = i + 2 from rfl] using this
  rw [mergeAt_def, htake, hci, hci1, hdrop]
  rw [show p + (q.getD i 0 - p) = q.getD i 0 by omega]
  exact decomp_at q i hq

/-! ### The vertex-pair flow on `Composition n` -/

variable {n : ℕ}

/-- Total flow on the cover edge from `q` to `c` (0 if not a cover):
sum of `F` over the splits realizing it (Draft Definition 4). -/
def fEdge (q c : Composition n) : ℚ :=
  ∑ i ∈ Finset.range q.blocks.length,
    ∑ p ∈ Finset.Icc 1 (q.blocks.getD i 0 - 1),
      if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0

lemma fEdge_nonneg (q c : Composition n) : 0 ≤ fEdge q c := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro p _
  by_cases h : splitAt q.blocks i p = c.blocks
  · rw [if_pos h]
    exact F_nonneg _ _ _
  · rw [if_neg h]

lemma comp_blocks_pos (c : Composition n) : ∀ x ∈ c.blocks, 1 ≤ x :=
  fun x hx => c.blocks_pos hx

/-- Outflow collapse: summing `fEdge q ·` over all compositions gives
`outSum q.blocks` (each admissible split lands on exactly one composition). -/
lemma sum_fEdge_out (q : Composition n) :
    ∑ c : Composition n, fEdge q c = outSum q.blocks := by
  unfold fEdge outSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases hF : F q.blocks i p = 0
  · rw [hF]
    apply Finset.sum_eq_zero
    intro c _
    split_ifs <;> rfl
  · -- valid split: build the child composition
    have hcond : Supp q.blocks ∧ 2 ≤ p ∧ 2 ≤ q.blocks.getD i 0 - p := by
      by_contra hc
      exact hF (by
        unfold F
        rw [indN_eq_zero _ _ _ hc, indFL_eq_zero _ _ _ hc,
            indFR_eq_zero _ _ _ hc]
        ring)
    have hi : i < q.blocks.length := by
      by_contra hle
      have := getD_eq_zero_of_le q.blocks i (by omega)
      omega
    have hsum : (splitAt q.blocks i p).sum = n := by
      rw [splitAt_sum q.blocks i p hi (by omega)]
      exact q.blocks_sum
    have hpos : ∀ x ∈ splitAt q.blocks i p, 0 < x := by
      intro x hx
      have := Supp_splitAt q.blocks i p hcond.1 hcond.2.1 hcond.2.2 x hx
      omega
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Composition n,
        c₀.blocks = splitAt q.blocks i p :=
      ⟨⟨splitAt q.blocks i p, fun {x} hx => hpos x hx, hsum⟩, rfl⟩
    have hiff : ∀ c : Composition n,
        (splitAt q.blocks i p = c.blocks) ↔ c = c₀ := by
      intro c
      constructor
      · intro h
        exact (Composition.ext (hc₀.trans h)).symm
      · rintro rfl
        exact hc₀.symm
    calc (∑ c : Composition n,
            if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0)
        = ∑ c : Composition n, if c = c₀ then F q.blocks i p else 0 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [if_congr (hiff c) rfl rfl]
      _ = F q.blocks i p := by
          rw [Finset.sum_ite_eq' Finset.univ c₀ (fun _ => F q.blocks i p)]
          exact if_pos (Finset.mem_univ c₀)

/-- Inner inflow collapse: for fixed `(i,p)`, at most one parent `q` can
split onto `c`, namely `mergeAt c i` with `p = c_i` (Draft Lemma 7). -/
lemma sum_fEdge_in_term (c : Composition n) (i p : ℕ) :
    (∑ q : Composition n,
      if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0)
    = if i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
      then F (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0 := by
  by_cases hcase : i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
  · obtain ⟨hilen, rfl⟩ := hcase
    rw [if_pos ⟨hilen, rfl⟩]
    -- the parent composition qM = mergeAt c i
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
    obtain ⟨qM, hqM⟩ : ∃ qM : Composition n,
        qM.blocks = mergeAt c.blocks i :=
      ⟨⟨mergeAt c.blocks i, fun {x} hx => hposM x hx, hsumM⟩, rfl⟩
    have hiff : ∀ q : Composition n,
        (splitAt q.blocks i (c.blocks.getD i 0) = c.blocks) ↔ q = qM := by
      intro q
      constructor
      · intro h
        have hvalid := splitAt_valid_of_pos q.blocks c.blocks i
          (c.blocks.getD i 0) (comp_blocks_pos c) h
        have hinv := splitAt_inversion q.blocks c.blocks i
          (c.blocks.getD i 0) hvalid.1 hvalid.2.1 hvalid.2.2 h
        exact Composition.ext (hinv.1.trans hqM.symm)
      · rintro rfl
        rw [hqM]
        exact splitAt_mergeAt c.blocks i hilen
    calc (∑ q : Composition n,
            if splitAt q.blocks i (c.blocks.getD i 0) = c.blocks
            then F q.blocks i (c.blocks.getD i 0) else 0)
        = ∑ q : Composition n,
            if q = qM then F (mergeAt c.blocks i) i (c.blocks.getD i 0)
            else 0 := by
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases h : q = qM
          · rw [if_pos ((hiff q).mpr h), if_pos h, h, hqM]
          · rw [if_neg (fun hc => h ((hiff q).mp hc)), if_neg h]
      _ = F (mergeAt c.blocks i) i (c.blocks.getD i 0) := by
          rw [Finset.sum_ite_eq' Finset.univ qM
            (fun _ => F (mergeAt c.blocks i) i (c.blocks.getD i 0))]
          exact if_pos (Finset.mem_univ qM)
  · rw [if_neg hcase]
    apply Finset.sum_eq_zero
    intro q _
    by_cases h : splitAt q.blocks i p = c.blocks
    · exfalso
      have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p
        (comp_blocks_pos c) h
      have hinv := splitAt_inversion q.blocks c.blocks i p
        hvalid.1 hvalid.2.1 hvalid.2.2 h
      exact hcase ⟨hinv.2.2, hinv.2.1.symm⟩
    · rw [if_neg h]

/-- `F` vanishes off the admissible offset window. -/
lemma F_eq_zero_outside (c : List ℕ) (i p : ℕ)
    (h : p ∉ Finset.Icc 1 (c.getD i 0 - 1)) : F c i p = 0 := by
  by_cases hc : Supp c ∧ 2 ≤ p ∧ 2 ≤ c.getD i 0 - p
  · exfalso
    apply h
    rw [Finset.mem_Icc]
    omega
  · unfold F
    rw [indN_eq_zero _ _ _ hc, indFL_eq_zero _ _ _ hc, indFR_eq_zero _ _ _ hc]
    ring

lemma comp_length_le (q : Composition n) : q.blocks.length ≤ n := by
  have h1 : ∀ (l : List ℕ), (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum := by
    intro l
    induction l with
    | nil => intro; simp
    | cons a t ih =>
      intro hpos
      have ha := hpos a List.mem_cons_self
      have := ih (fun x hx => hpos x (List.mem_cons_of_mem a hx))
      simp [List.sum_cons]
      omega
  have := h1 q.blocks (comp_blocks_pos q)
  rwa [q.blocks_sum] at this

lemma comp_getD_le (q : Composition n) (i : ℕ) : q.blocks.getD i 0 ≤ n := by
  by_cases hi : i < q.blocks.length
  · have := mem_le_sum (getD_mem q.blocks i hi)
    rwa [q.blocks_sum] at this
  · rw [getD_eq_zero_of_le q.blocks i (by omega)]
    omega

/-- Inflow collapse: summing `fEdge · c` over all compositions gives
`inSum c.blocks` (Draft Lemma 7, totalized). -/
lemma sum_fEdge_in (c : Composition n) :
    ∑ q : Composition n, fEdge q c = inSum c.blocks := by
  have hT : ∀ q : Composition n, fEdge q c
      = ∑ i ∈ Finset.range n, ∑ p ∈ Finset.range (n + 1),
          (if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0) := by
    intro q
    unfold fEdge
    have step1 : ∀ i,
        (∑ p ∈ Finset.Icc 1 (q.blocks.getD i 0 - 1),
          if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0)
        = ∑ p ∈ Finset.range (n + 1),
            if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0 := by
      intro i
      apply Finset.sum_subset
      · intro p hp
        rw [Finset.mem_Icc] at hp
        rw [Finset.mem_range]
        have := comp_getD_le q i
        omega
      · intro p _ hp
        by_cases hsp : splitAt q.blocks i p = c.blocks
        · rw [if_pos hsp, F_eq_zero_outside q.blocks i p hp]
        · rw [if_neg hsp]
    rw [Finset.sum_congr rfl (fun i _ => step1 i)]
    apply Finset.sum_subset
    · intro x hx
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (comp_length_le q))
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro p _
      have hle : q.blocks.length ≤ i := by
        by_contra hlt
        exact hi (Finset.mem_range.mpr (by omega))
      have hzero : F q.blocks i p = 0 := by
        apply F_eq_zero_of_small
        rw [getD_eq_zero_of_le q.blocks i hle]
        omega
      by_cases hsp : splitAt q.blocks i p = c.blocks
      · rw [if_pos hsp, hzero]
      · rw [if_neg hsp]
  rw [Finset.sum_congr rfl (fun q _ => hT q)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm (s := Finset.univ)
    (t := Finset.range (n + 1)) (f := fun (q : Composition n) (p : ℕ) =>
      if splitAt q.blocks i p = c.blocks then F q.blocks i p else 0))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun p _ => sum_fEdge_in_term c i p))]
  -- collapse the p-sum, then match inSum
  have hstep2 : ∀ i,
      (∑ p ∈ Finset.range (n + 1),
        if i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0
        then F (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0)
      = (if i + 1 < c.blocks.length
         then F (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0) := by
    intro i
    by_cases hil : i + 1 < c.blocks.length
    · rw [if_pos hil]
      have : ∀ p, (i + 1 < c.blocks.length ∧ p = c.blocks.getD i 0)
          ↔ p = c.blocks.getD i 0 := fun p => and_iff_right hil
      rw [Finset.sum_congr rfl (fun p _ => if_congr (this p) rfl rfl)]
      rw [Finset.sum_ite_eq' (Finset.range (n + 1)) (c.blocks.getD i 0)
        (fun _ => F (mergeAt c.blocks i) i (c.blocks.getD i 0))]
      rw [if_pos (Finset.mem_range.mpr (by
        have := comp_getD_le c i
        omega))]
    · rw [if_neg hil]
      apply Finset.sum_eq_zero
      intro p _
      rw [if_neg (by tauto)]
  rw [Finset.sum_congr rfl (fun i _ => hstep2 i)]
  -- finally: restrict the range back to c.length − 1
  unfold inSum
  symm
  have hgoal : ∀ i ∈ Finset.range (c.blocks.length - 1),
      F (mergeAt c.blocks i) i (c.blocks.getD i 0)
        = (if i + 1 < c.blocks.length
           then F (mergeAt c.blocks i) i (c.blocks.getD i 0) else 0) := by
    intro i hi
    rw [if_pos (by
      have := Finset.mem_range.1 hi
      omega)]
  rw [Finset.sum_congr rfl hgoal]
  apply Finset.sum_subset
  · intro x hx
    refine Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) ?_)
    have := comp_length_le c
    omega
  · intro i _ hi
    rw [if_neg (by
      have hle : c.blocks.length - 1 ≤ i := by
        by_contra hlt
        exact hi (Finset.mem_range.mpr (by omega))
      omega)]

/-! ### Divergence bridge and the final theorems -/

/-- Divergence of `fEdge` equals `w` at every composition (`n ≥ 3`,
i.e. `d ≥ 1`).  This is Draft Theorem 1's identity (D). -/
lemma fEdge_div (hn : 3 ≤ n) (v : Composition n) :
    (∑ u : Composition n, fEdge v u) - (∑ u : Composition n, fEdge u v)
      = w v.blocks := by
  rw [sum_fEdge_out v, sum_fEdge_in v]
  have h := flowDiv_eq_w_all v.blocks
    (fun m hm => v.blocks_pos hm)
    (by rw [v.blocks_sum]; omega)
  unfold flowDiv at h
  exact h

/-- Nonzero flow edges are genuine Boolean covers (one valid split), so
the monotonicity hypothesis below is an instance of Cheng–Lin Lemma 3.29. -/
lemma fEdge_ne_zero_cover (q c : Composition n) (h : fEdge q c ≠ 0) :
    ∃ i p, i < q.blocks.length ∧ 1 ≤ p ∧ p < q.blocks.getD i 0 ∧
      splitAt q.blocks i p = c.blocks := by
  obtain ⟨i, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨p, _, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  by_cases hsp : splitAt q.blocks i p = c.blocks
  · have hvalid := splitAt_valid_of_pos q.blocks c.blocks i p
      (comp_blocks_pos c) hsp
    exact ⟨i, p, hvalid.1, hvalid.2.1, hvalid.2.2, hsp⟩
  · rw [if_neg hsp] at hne2
    exact absurd rfl hne2

/-- **Machine-checked certificate for Conjecture 3.30** (Draft Thm 1/1′).
For every `n = d + 2 ≥ 3`: the explicit flow `fEdge` is nonnegative, its
divergence is `w`, and consequently for any `N U : Composition n → ℚ`
with `U ≠ 0` satisfying the monotonicity inequalities along flow edges
(supplied for flag counts by Cheng–Lin Lemma 3.29, the external
hypothesis), the weighted sum `Σ (w/U)·N` is EXACTLY the nonnegative
combination of monotonicity differences, hence `≤ 0`. -/
theorem conjecture_3_30_certificate (hn : 3 ≤ n)
    (N U : Composition n → ℚ) (hU : ∀ v, U v ≠ 0)
    (hmono : ∀ q c : Composition n, fEdge q c ≠ 0 → N q / U q ≤ N c / U c) :
    (∑ v : Composition n, (w v.blocks / U v) * N v
      = ∑ v : Composition n, ∑ u : Composition n,
          fEdge v u * (N v / U v - N u / U u))
    ∧ ∑ v : Composition n, (w v.blocks / U v) * N v ≤ 0 :=
  ⟨conjecture_combination fEdge (fun v => w v.blocks) N U (fEdge_div hn) hU,
   conjecture_nonpos fEdge (fun v => w v.blocks) N U (fEdge_div hn)
     (fun u v => fEdge_nonneg u v) hU hmono⟩

end ChowCone
