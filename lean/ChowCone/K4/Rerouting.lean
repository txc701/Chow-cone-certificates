/-
The zero-divergence rerouting of Section 7 and the flow `f_d`.

Manuscript of 21 November 2026: Section 7.  The left square (28)–(29) of a
nonfinal or final-left `F_4` occurrence, the final-right square (31), the
cascade squares (32)–(33), the definition of `f_d` as `f_0` plus all these
corrections, and equation (34): `div f_d = w^{(4)}`.

Scope.  This file defines the corrections and `f_d` and proves (34) for
`d ≥ 3`.  It does not prove that `f_d` is nonnegative (Section 8), and it
does not treat `d = 1, 2`.
-/
import ChowCone.K4.SignedFlow
import ChowCone.K4.SquareCharges

namespace ChowCone
namespace K4

open Finset

/-! ### Linearity of the divergence -/

lemma outSumOf_add (f g : EdgeFlow) (c : List ℕ) :
    outSumOf (f + g) c = outSumOf f c + outSumOf g c := by
  simp only [outSumOf, Pi.add_apply, sum_add_distrib]

lemma inSumOf_add (f g : EdgeFlow) (c : List ℕ) :
    inSumOf (f + g) c = inSumOf f c + inSumOf g c := by
  simp only [inSumOf, Pi.add_apply, sum_add_distrib]

lemma divOf_add (f g : EdgeFlow) (c : List ℕ) : divOf (f + g) c = divOf f c + divOf g c := by
  unfold divOf
  rw [outSumOf_add, inSumOf_add]
  ring

lemma divOf_smul (a : ℚ) (f : EdgeFlow) (c : List ℕ) : divOf (a • f) c = a * divOf f c := by
  simp only [divOf, outSumOf, inSumOf, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  ring

lemma divOf_sub (f g : EdgeFlow) (c : List ℕ) : divOf (f - g) c = divOf f c - divOf g c := by
  simp only [divOf, outSumOf, inSumOf, Pi.sub_apply, sum_sub_distrib]
  ring

lemma divOf_zero (c : List ℕ) : divOf (0 : EdgeFlow) c = 0 := by
  simp [divOf, outSumOf, inSumOf]

lemma divOf_sum {ι : Type*} (S : Finset ι) (f : ι → EdgeFlow) (c : List ℕ) :
    divOf (∑ s ∈ S, f s) c = ∑ s ∈ S, divOf (f s) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [divOf_zero]
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, divOf_add, ih]

/-! ### Positional edges and unit flows -/

/-- A positional edge: split block `idx` of `parent` at offset `off`. -/
structure PEdge where
  parent : List ℕ
  idx : ℕ
  off : ℕ
  deriving DecidableEq, Repr

/-- The child of a positional edge. -/
def PEdge.child (e : PEdge) : List ℕ := splitAt e.parent e.idx e.off

/-- The edge is a legal split: the block exists and both parts are positive. -/
def PEdge.Valid (e : PEdge) : Prop :=
  e.idx < e.parent.length ∧ 1 ≤ e.off ∧ e.off < e.parent.getD e.idx 0

/-- The edge of a tagged occurrence. -/
def Occ.edge (o : Occ) : PEdge := ⟨o.parent, o.idx, o.offset⟩

theorem Occ.edge_child (o : Occ) : o.edge.child = o.child := rfl

/-- The unit flow `[A → B]` on a positional edge. -/
def edgeUnit (e : PEdge) : EdgeFlow := fun c i p =>
  if c = e.parent ∧ i = e.idx ∧ p = e.off then 1 else 0

lemma outSumOf_edgeUnit (e : PEdge) (he : e.Valid) (c : List ℕ) :
    outSumOf (edgeUnit e) c = if c = e.parent then 1 else 0 := by
  unfold outSumOf edgeUnit
  by_cases hc : c = e.parent
  · subst hc
    rw [if_pos rfl,
      sum_eq_single_of_mem e.idx (mem_range.2 he.1)
        (fun i _ hi => sum_eq_zero fun p _ => if_neg fun h => hi h.2.1),
      sum_eq_single_of_mem e.off (mem_Icc.2 ⟨he.2.1, by have := he.2.2; omega⟩)
        (fun p _ hp => if_neg fun h => hp h.2.2),
      if_pos ⟨rfl, rfl, rfl⟩]
  · rw [if_neg hc]
    exact sum_eq_zero fun i _ => sum_eq_zero fun p _ => if_neg fun h => hc h.1

lemma inSumOf_edgeUnit (e : PEdge) (he : e.Valid) (c : List ℕ) :
    inSumOf (edgeUnit e) c = if c = e.child then 1 else 0 := by
  unfold inSumOf edgeUnit
  by_cases hc : c = e.child
  · rw [if_pos hc]
    obtain ⟨hq, hget, hlen⟩ :=
      splitAt_inversion e.parent c e.idx e.off he.1 he.2.1 he.2.2 hc.symm
    rw [sum_eq_single_of_mem e.idx (mem_range.2 (by omega))
        (fun i _ hi => if_neg fun h => hi h.2.1),
      if_pos ⟨hq.symm, rfl, hget⟩]
  · rw [if_neg hc]
    refine sum_eq_zero fun i hi => if_neg fun h => hc ?_
    have hlt : i + 1 < c.length := by
      have := mem_range.1 hi
      omega
    have h1 := splitAt_mergeAt c i hlt
    rw [h.1, h.2.2, h.2.1] at h1
    exact h1.symm

/-- The divergence of a unit flow: `+1` at the parent, `-1` at the child. -/
theorem divOf_edgeUnit (e : PEdge) (he : e.Valid) (c : List ℕ) :
    divOf (edgeUnit e) c = (if c = e.parent then 1 else 0) - (if c = e.child then 1 else 0) := by
  unfold divOf
  rw [outSumOf_edgeUnit e he, inSumOf_edgeUnit e he]

/-- The difference of the edge chains of two paths `A → B → D` and
`A → C → D`. -/
def squareFlow (e1 e2 e3 e4 : PEdge) : EdgeFlow :=
  edgeUnit e1 + edgeUnit e2 - edgeUnit e3 - edgeUnit e4

/-- A path square has zero divergence. -/
theorem divOf_squareFlow (e1 e2 e3 e4 : PEdge) (h1 : e1.Valid) (h2 : e2.Valid)
    (h3 : e3.Valid) (h4 : e4.Valid) (h12 : e2.parent = e1.child)
    (h13 : e3.parent = e1.parent) (h34 : e4.parent = e3.child) (h24 : e4.child = e2.child)
    (c : List ℕ) : divOf (squareFlow e1 e2 e3 e4) c = 0 := by
  unfold squareFlow
  rw [divOf_sub, divOf_sub, divOf_add, divOf_edgeUnit e1 h1, divOf_edgeUnit e2 h2,
    divOf_edgeUnit e3 h3, divOf_edgeUnit e4 h4, h12, h13, h34, h24]
  ring

lemma pedge_valid_append (Q S : List ℕ) (m p : ℕ) (h1 : 1 ≤ p) (h2 : p < m) :
    (⟨Q ++ m :: S, Q.length, p⟩ : PEdge).Valid := by
  refine ⟨by simp, h1, ?_⟩
  show p < (Q ++ m :: S).getD Q.length 0
  rw [getD_append_length]
  exact h2

lemma getD_append_length_succ' (Q S : List ℕ) (a m : ℕ) :
    (Q ++ a :: m :: S).getD (Q.length + 1) 0 = m := by
  simp

lemma pedge_valid_append_succ (Q S : List ℕ) (a m p : ℕ) (h1 : 1 ≤ p) (h2 : p < m) :
    (⟨Q ++ a :: m :: S, Q.length + 1, p⟩ : PEdge).Valid := by
  refine ⟨by simp, h1, ?_⟩
  show p < (Q ++ a :: m :: S).getD (Q.length + 1) 0
  rw [getD_append_length_succ']
  exact h2

/-! ### The left square of a nonfinal or final-left `F_4` occurrence -/

/-- `A → B`, the `F_4` occurrence itself. -/
def LeftSource.eAB (s : LeftSource) : PEdge := ⟨s.P ++ (s.t + 4) :: s.S, s.P.length, 4⟩
/-- `B → D`, the split `4 ↦ (2,2)`. -/
def LeftSource.eBD (s : LeftSource) : PEdge := ⟨s.P ++ 4 :: s.t :: s.S, s.P.length, 2⟩
/-- `A → C`, the left peel `(t+4) ↦ (2,t+2)`. -/
def LeftSource.eAC (s : LeftSource) : PEdge := ⟨s.P ++ (s.t + 4) :: s.S, s.P.length, 2⟩
/-- `C → D`, the left peel `(t+2) ↦ (2,t)`. -/
def LeftSource.eCD (s : LeftSource) : PEdge :=
  ⟨s.P ++ 2 :: (s.t + 2) :: s.S, s.P.length + 1, 2⟩

/-- The path square (29), with unit coefficient. -/
def LeftSource.square (s : LeftSource) : EdgeFlow := squareFlow s.eAB s.eBD s.eAC s.eCD

/-- `R = 48 G(B)`. -/
def LeftSource.rawDebit (s : LeftSource) : ℚ := 48 * G s.occ.child

theorem LeftSource.eAB_eq (s : LeftSource) : s.eAB = s.occ.edge := by
  simp only [LeftSource.eAB, Occ.edge, LeftSource.occ, PEdge.mk.injEq, true_and]
  exact (offset_left s.occ (leftTag_ne_finalRight s.S)).symm

theorem LeftSource.eAC_eq (s : LeftSource) : s.eAC = s.row1Label.edge := by
  simp only [LeftSource.eAC, Occ.edge, LeftSource.row1Label, PEdge.mk.injEq, true_and]
  exact (offset_left s.row1Label (leftTag_ne_finalRight s.S)).symm

theorem LeftSource.eCD_eq (s : LeftSource) : s.eCD = s.row2Label.edge := by
  simp only [LeftSource.eCD, Occ.edge, LeftSource.row2Label, PEdge.mk.injEq, true_and]
  exact (offset_left s.row2Label (leftTag_ne_finalRight s.S)).symm

theorem LeftSource.divOf_square (s : LeftSource) (ht : 1 ≤ s.t) (c : List ℕ) :
    divOf s.square c = 0 := by
  have e1 : s.t + 4 - 4 = s.t := by omega
  have e2 : s.t + 4 - 2 = s.t + 2 := by omega
  have e3 : s.t + 2 - 2 = s.t := by omega
  refine divOf_squareFlow _ _ _ _
    (pedge_valid_append s.P s.S (s.t + 4) 4 (by norm_num) (by omega))
    (pedge_valid_append s.P (s.t :: s.S) 4 2 (by norm_num) (by norm_num))
    (pedge_valid_append s.P s.S (s.t + 4) 2 (by norm_num) (by omega))
    (pedge_valid_append_succ s.P s.S 2 (s.t + 2) 2 (by norm_num) (by omega))
    ?_ rfl ?_ ?_ c
  · show s.P ++ 4 :: s.t :: s.S = splitAt (s.P ++ (s.t + 4) :: s.S) s.P.length 4
    rw [splitAt_append, e1]
  · show s.P ++ 2 :: (s.t + 2) :: s.S = splitAt (s.P ++ (s.t + 4) :: s.S) s.P.length 2
    rw [splitAt_append, e2]
  · show splitAt (s.P ++ 2 :: (s.t + 2) :: s.S) (s.P.length + 1) 2
      = splitAt (s.P ++ 4 :: s.t :: s.S) s.P.length 2
    rw [splitAt_append_succ, splitAt_append, e3]

/-! ### The final-right square -/

/-- `A → B`, the final-right `F_4` occurrence `(t+4) ↦ (t,4)`. -/
def Source.eAB (s : Source) : PEdge := ⟨s.P ++ [s.t + 4], s.P.length, s.t⟩
/-- `B → D`, the split `4 ↦ (2,2)` of the final block. -/
def Source.eBD (s : Source) : PEdge := ⟨s.P ++ [s.t, 4], s.P.length + 1, 2⟩
/-- `A → C`, the right peel `(t+4) ↦ (t+2,2)`. -/
def Source.eAC (s : Source) : PEdge := ⟨s.P ++ [s.t + 4], s.P.length, s.t + 2⟩
/-- `C → D`, the right peel `(t+2) ↦ (t,2)`: the edge that keeps the debt. -/
def Source.eCD (s : Source) : PEdge := ⟨s.P ++ [s.t + 2, 2], s.P.length, s.t⟩

/-- The final-right path square (31), with unit coefficient. -/
def Source.square (s : Source) : EdgeFlow := squareFlow s.eAB s.eBD s.eAC s.eCD

theorem Source.eAB_eq (s : Source) : s.eAB = s.occ.edge := by
  simp only [Source.eAB, Occ.edge, Source.occ, Occ.offset, getD_append_length, PEdge.mk.injEq,
    true_and]
  omega

theorem Source.eAC_eq (s : Source) : s.eAC = s.row3Label.edge := by
  simp only [Source.eAC, Occ.edge, Source.row3Label, Occ.offset, getD_append_length,
    PEdge.mk.injEq, true_and]
  omega

theorem Source.divOf_square (s : Source) (ht : 1 ≤ s.t) (c : List ℕ) :
    divOf s.square c = 0 := by
  have e1 : s.t + 4 - s.t = 4 := by omega
  have e2 : s.t + 4 - (s.t + 2) = 2 := by omega
  have e3 : s.t + 2 - s.t = 2 := by omega
  refine divOf_squareFlow _ _ _ _
    (pedge_valid_append s.P [] (s.t + 4) s.t ht (by omega))
    (pedge_valid_append_succ s.P [] s.t 4 2 (by norm_num) (by norm_num))
    (pedge_valid_append s.P [] (s.t + 4) (s.t + 2) (by omega) (by omega))
    (pedge_valid_append s.P [2] (s.t + 2) s.t ht (by omega))
    ?_ rfl ?_ ?_ c
  · show s.P ++ [s.t, 4] = splitAt (s.P ++ [s.t + 4]) s.P.length s.t
    rw [splitAt_append, e1]
  · show s.P ++ [s.t + 2, 2] = splitAt (s.P ++ [s.t + 4]) s.P.length (s.t + 2)
    rw [splitAt_append, e2]
  · show splitAt (s.P ++ [s.t + 2, 2]) s.P.length s.t
      = splitAt (s.P ++ [s.t, 4]) (s.P.length + 1) 2
    rw [splitAt_append_succ, splitAt_append, e3]

/-! ### The cascade squares -/

/-- `X → Y`, the right peel that carries the debt at the state `(Q, y)`. -/
def cXY (Q : List ℕ) (y : ℕ) : PEdge := ⟨sqX Q y, Q.length, y⟩
/-- `Y → W`. -/
def cYW (Q : List ℕ) (y : ℕ) : PEdge := ⟨sqY Q y, Q.length, 2⟩
/-- `X → Z`, the consumed left `F_2` occurrence. -/
def cXZ (Q : List ℕ) (y : ℕ) : PEdge := ⟨sqX Q y, Q.length, 2⟩
/-- `Z → W`, the right peel that receives the debt. -/
def cZW (Q : List ℕ) (y : ℕ) : PEdge := ⟨sqZ Q y, Q.length + 1, y - 2⟩

/-- The cascade square (33) at the state `(Q, y)`, with unit coefficient. -/
def cascSquare (Q : List ℕ) (y : ℕ) : EdgeFlow :=
  squareFlow (cXY Q y) (cYW Q y) (cXZ Q y) (cZW Q y)

/-- All cascade squares of the cascade started at `(Q, y)`: one square at
each state with parameter at least 4. -/
def cascadeFlow (Q : List ℕ) : ℕ → EdgeFlow
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | y + 4 => cascSquare Q (y + 4) + cascadeFlow (Q ++ [2]) (y + 2)

/-- The debt left by the final-right square is on the first cascade edge. -/
theorem Source.eCD_eq (s : Source) : s.eCD = cXY s.P s.t := rfl

/-- The consumed edge of a cascade square is the edge of the row-4 label. -/
theorem cXZ_eq (Q : List ℕ) (y : ℕ) : cXZ Q y = (leftF2 Q y).edge := rfl

/-- At `y = 2` the debt edge is the edge of the row-5 label. -/
theorem cXY_two (Q : List ℕ) : cXY Q 2 = (leftF2 Q 2).edge := rfl

/-- At `y = 3` the debt edge is the edge of the row-6 label. -/
theorem cXY_three (Q : List ℕ) : cXY Q 3 = (nonfinalF3 Q).edge := rfl

/-- The debt moves to the debt edge of the next state: `Z_j → W_j` is
`X_{j+1} → Y_{j+1}`. -/
theorem cZW_eq_cXY_next (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    cZW Q y = cXY (Q ++ [2]) (y - 2) := by
  simp only [cZW, cXY, sqZ_eq_sqX_next Q y hy, List.length_append, List.length_cons,
    List.length_nil]

theorem divOf_cascSquare (Q : List ℕ) (y : ℕ) (hy : 4 ≤ y) (c : List ℕ) :
    divOf (cascSquare Q y) c = 0 := by
  refine divOf_squareFlow _ _ _ _
    (pedge_valid_append Q [2] (y + 2) y (by omega) (by omega))
    (pedge_valid_append Q [2, 2] y 2 (by norm_num) (by omega))
    (pedge_valid_append Q [2] (y + 2) 2 (by norm_num) (by omega))
    (pedge_valid_append_succ Q [2] 2 y (y - 2) (by omega) (by omega))
    (sqY_eq_splitAt Q y) rfl (sqZ_eq_splitAt Q y) ?_ c
  exact (sqW_eq_splitAt_sqZ Q y (by omega)).symm.trans (sqW_eq_splitAt_sqY Q y)

theorem divOf_cascadeFlow (Q : List ℕ) (y : ℕ) (c : List ℕ) :
    divOf (cascadeFlow Q y) c = 0 := by
  induction Q, y using cascadeFlow.induct with
  | case1 => rw [cascadeFlow, divOf_zero]
  | case2 => rw [cascadeFlow, divOf_zero]
  | case3 => rw [cascadeFlow, divOf_zero]
  | case4 => rw [cascadeFlow, divOf_zero]
  | case5 Q y ih =>
    rw [cascadeFlow, divOf_add, divOf_cascSquare Q (y + 4) (by omega), ih, add_zero]

/-! ### All sources at a given size -/

lemma length_le_sum {P : List ℕ} (h : ∀ m ∈ P, 1 ≤ m) : P.length ≤ P.sum := by
  induction P with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun m hm => h m (List.mem_cons_of_mem a hm)
    simp only [List.length_cons, List.sum_cons]
    omega

/-- There are finitely many nonfinal and final-left sources at size `N`. -/
theorem validLeftSources_finite (N : ℕ) : {s : LeftSource | s.Valid N}.Finite := by
  have hfin : ((Set.range fun c : Composition N => c.blocks) ×ˢ Set.Iic N).Finite :=
    (Set.finite_range _).prod (Set.finite_Iic N)
  refine Set.Finite.of_finite_image
    (f := fun s : LeftSource => (s.P ++ (s.t + 4) :: s.S, s.P.length)) (hfin.subset ?_) ?_
  · rintro ⟨c, k⟩ ⟨s, ⟨hP, hS, ht, hsum⟩, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨⟨s.P ++ (s.t + 4) :: s.S, ?_, ?_⟩, rfl⟩, ?_⟩
    · intro i hi
      rcases List.mem_append.1 hi with h | h
      · have := hP i h
        omega
      · rcases List.mem_cons.1 h with h | h
        · omega
        · have := hS i h
          omega
    · rw [sum_decomp]
      exact hsum
    · have h1 : s.P.length ≤ s.P.sum := length_le_sum fun m hm => by
        have := hP m hm
        omega
      show s.P.length ≤ N
      omega
  · rintro ⟨P, t, S⟩ _ ⟨P', t', S'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := List.append_inj h1 h2
    simp only [List.cons.injEq] at h3
    obtain ⟨rfl, h4, rfl⟩ := h3
    have : t = t' := by omega
    subst this
    rfl

/-- The nonfinal and final-left `F_4` sources at size `N`. -/
noncomputable def leftSources (N : ℕ) : Finset LeftSource := (validLeftSources_finite N).toFinset

/-- The final-right `F_4` sources at size `N`. -/
noncomputable def rightSources (N : ℕ) : Finset Source := (validSources_finite N).toFinset

theorem mem_leftSources {N : ℕ} {s : LeftSource} : s ∈ leftSources N ↔ s.Valid N :=
  Set.Finite.mem_toFinset _

theorem mem_rightSources {N : ℕ} {s : Source} : s ∈ rightSources N ↔ s.Valid N :=
  Set.Finite.mem_toFinset _

/-! ### The flow `f_d` -/

/-- The flow `f_d` on the compositions of `N = d + 2`: `f_0` plus the left
square of every nonfinal and final-left `F_4` occurrence, plus the
final-right square and all cascade squares of every final-right `F_4`
occurrence, each with coefficient `R = 48 G(B)`. -/
noncomputable def fd (N : ℕ) : EdgeFlow :=
  f0 + ∑ s ∈ leftSources N, s.rawDebit • s.square
    + ∑ s ∈ rightSources N, s.rawDebit • (s.square + cascadeFlow s.P s.t)

/-- The corrections have zero divergence. -/
theorem divOf_fd_eq_divOf_f0 (N : ℕ) (c : List ℕ) : divOf (fd N) c = divOf f0 c := by
  unfold fd
  rw [divOf_add, divOf_add, divOf_sum, divOf_sum]
  have hL : ∀ s ∈ leftSources N, divOf (s.rawDebit • s.square) c = 0 := by
    intro s hs
    have hv := mem_leftSources.1 hs
    rw [divOf_smul, s.divOf_square (by have := hv.2.2.1; omega), mul_zero]
  have hR : ∀ s ∈ rightSources N,
      divOf (s.rawDebit • (s.square + cascadeFlow s.P s.t)) c = 0 := by
    intro s hs
    have hv := mem_rightSources.1 hs
    rw [divOf_smul, divOf_add, s.divOf_square (by have := hv.2.1; omega), divOf_cascadeFlow,
      add_zero, mul_zero]
  rw [sum_eq_zero hL, sum_eq_zero hR, add_zero, add_zero]

/-- **Equation (34).**  For `d ≥ 3` and `N = d + 2`, `div f_d = w^{(4)}` at
every support composition of `N`. -/
theorem divOf_fd (d : ℕ) (hd : 3 ≤ d) (c : List ℕ) (hs : Supp c) (hN : c.sum = d + 2) :
    divOf (fd (d + 2)) c = w4 c := by
  rw [divOf_fd_eq_divOf_f0]
  exact divOf_f0 c hs (by omega)

/-! ### The vertices of the squares are support compositions -/

theorem LeftSource.square_supp (s : LeftSource) (N : ℕ) (hv : s.Valid N) :
    Supp s.eAB.parent ∧ Supp s.eAB.child ∧ Supp s.eAC.child ∧ Supp s.eBD.child := by
  obtain ⟨hP, hS, ht, -⟩ := hv
  have e1 : s.t + 4 - 4 = s.t := by omega
  have e2 : s.t + 4 - 2 = s.t + 2 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, hS⟩⟩
  · show Supp (splitAt (s.P ++ (s.t + 4) :: s.S) s.P.length 4)
    rw [splitAt_append, e1]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨ht, hS⟩⟩⟩
  · show Supp (splitAt (s.P ++ (s.t + 4) :: s.S) s.P.length 2)
    rw [splitAt_append, e2]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨by omega, hS⟩⟩⟩
  · show Supp (splitAt (s.P ++ 4 :: s.t :: s.S) s.P.length 2)
    rw [splitAt_append]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨by norm_num,
      supp_cons.2 ⟨ht, hS⟩⟩⟩⟩

lemma supp_nil : Supp [] := fun _ h => by simp at h

theorem Source.square_supp (s : Source) (N : ℕ) (hv : s.Valid N) :
    Supp s.eAB.parent ∧ Supp s.eAB.child ∧ Supp s.eAC.child ∧ Supp s.eBD.child := by
  obtain ⟨hP, ht, -⟩ := hv
  have e1 : s.t + 4 - s.t = 4 := by omega
  have e2 : s.t + 4 - (s.t + 2) = 2 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, supp_nil⟩⟩
  · show Supp (splitAt (s.P ++ [s.t + 4]) s.P.length s.t)
    rw [splitAt_append, e1]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨ht, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩
  · show Supp (splitAt (s.P ++ [s.t + 4]) s.P.length (s.t + 2))
    rw [splitAt_append, e2]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩
  · show Supp (splitAt (s.P ++ [s.t, 4]) (s.P.length + 1) 2)
    rw [splitAt_append_succ]
    exact supp_append.2 ⟨hP, supp_cons.2 ⟨ht, supp_cons.2 ⟨by norm_num,
      supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩⟩

/-- The vertices `X, Y, Z, W` of a cascade square are support compositions. -/
theorem cascSquare_supp (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 4 ≤ y) :
    Supp (sqX Q y) ∧ Supp (sqY Q y) ∧ Supp (sqZ Q y) ∧ Supp (sqW Q y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact supp_append.2 ⟨hQ, supp_cons.2 ⟨by omega, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩
  · exact supp_append.2 ⟨hQ, supp_cons.2 ⟨by omega, supp_cons.2 ⟨by norm_num,
      supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩⟩
  · exact supp_append.2 ⟨hQ, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨by omega,
      supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩⟩
  · exact supp_append.2 ⟨hQ, supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨by omega,
      supp_cons.2 ⟨by norm_num, supp_cons.2 ⟨by norm_num, supp_nil⟩⟩⟩⟩⟩

end K4
end ChowCone
