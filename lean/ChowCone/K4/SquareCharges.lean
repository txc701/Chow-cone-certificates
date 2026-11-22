/-
Origins of the charges of rows 1–3 of Table 1.

Manuscript of 21 November 2026: Section 7, the left square (28)–(29) for a
nonfinal or final-left `F_4` occurrence, `A = P.(t+4).S, B = P.(4,t).S,
C = P.(2,t+2).S, D = P.(2,2,t).S`; the final-right square (31); rows 1–3 of
Table 1 and the sentence after it: "For types 1–3, the charged occurrence
and the type determine the origin, if one exists."

Scope.  This file verifies, for each of the rows 1–3, which labels are
charged and that a label has at most one origin.  It does not formalize the
amounts (30) of these charges, any inequality, or any statement about
divergence.
-/
import ChowCone.K4.CascadeOrigins

namespace ChowCone
namespace K4

/-! ### Sources of the left square: nonfinal and final-left `F_4` occurrences -/

/-- The tag of a left peel of a block followed by the blocks `S`: final-left
when `S` is empty, nonfinal otherwise. -/
def leftTag (S : List ℕ) : Tag := if S = [] then .finalLeft else .nonfinal

/-- A nonfinal or final-left `F_4` occurrence, on the block `t+4` of
`A = P.(t+4).S`. -/
structure LeftSource where
  P : List ℕ
  t : ℕ
  S : List ℕ
  deriving DecidableEq, Repr

/-- The source lives at total size `N`. -/
def LeftSource.Valid (N : ℕ) (s : LeftSource) : Prop :=
  Supp s.P ∧ Supp s.S ∧ 2 ≤ s.t ∧ s.P.sum + (s.t + 4) + s.S.sum = N

/-- The `F_4` occurrence `A → B`, `(t+4) ↦ (4,t)`. -/
def LeftSource.occ (s : LeftSource) : Occ :=
  ⟨4, leftTag s.S, s.P ++ (s.t + 4) :: s.S, s.P.length⟩

/-- Row 1: the left `F_2` occurrence of the block `t+4` of `A`; its edge is
`A → C`. -/
def LeftSource.row1Label (s : LeftSource) : Occ :=
  ⟨2, leftTag s.S, s.P ++ (s.t + 4) :: s.S, s.P.length⟩

/-- Row 2: the left `F_2` occurrence of the block `t+2` of
`C = P.(2,t+2).S`; its edge is `C → D`. -/
def LeftSource.row2Label (s : LeftSource) : Occ :=
  ⟨2, leftTag s.S, s.P ++ 2 :: (s.t + 2) :: s.S, s.P.length + 1⟩

/-- Row 3: the right `F_2` occurrence of the final block `t+4` of
`A = P.(t+4)`; its edge is `A → C` of the final-right square. -/
def Source.row3Label (s : Source) : Occ :=
  ⟨2, .finalRight, s.P ++ [s.t + 4], s.P.length⟩

/-- The three rows treated here. -/
inductive TopRow
  | row1
  | row2
  | row3
  deriving DecidableEq, Repr

/-- A charge of rows 1–3. -/
structure TopCharge where
  row : TopRow
  label : Occ
  deriving DecidableEq, Repr

/-- The charges made by the left square of a nonfinal or final-left source,
with multiplicity. -/
def LeftSource.charges (s : LeftSource) : List TopCharge :=
  [⟨.row1, s.row1Label⟩, ⟨.row2, s.row2Label⟩]

/-- The charge made by the initial square of a final-right source. -/
def Source.topCharges (s : Source) : List TopCharge := [⟨.row3, s.row3Label⟩]

/-! ### Helpers -/

lemma leftTag_nil : leftTag [] = .finalLeft := rfl

lemma leftTag_of_ne {S : List ℕ} (h : S ≠ []) : leftTag S = .nonfinal := by
  simp [leftTag, h]

lemma leftTag_ne_finalRight (S : List ℕ) : leftTag S ≠ .finalRight := by
  unfold leftTag
  split_ifs <;> simp

lemma splitAt_append_succ (Q S : List ℕ) (a m p : ℕ) :
    splitAt (Q ++ a :: m :: S) (Q.length + 1) p = Q ++ a :: p :: (m - p) :: S := by
  have h := splitAt_append (Q ++ [a]) S m p
  simpa using h

/-- The position condition of `Occ.Selected` for a left tag. -/
lemma leftTag_position (P S : List ℕ) (m : ℕ) :
    match leftTag S with
    | .nonfinal => P.length + 1 < (P ++ m :: S).length
    | _ => P.length + 1 = (P ++ m :: S).length := by
  unfold leftTag
  split_ifs with h
  · subst h; simp
  · have : 0 < S.length := List.length_pos_iff.2 h
    simp only [List.length_append, List.length_cons]
    omega

lemma supp_cons {a : ℕ} {S : List ℕ} : Supp (a :: S) ↔ 2 ≤ a ∧ Supp S := by
  unfold Supp
  simp

lemma offset_left (o : Occ) (h : o.tag ≠ .finalRight) : o.offset = o.s := by
  unfold Occ.offset
  cases ht : o.tag <;> simp_all

/-! ### The edges of the left square -/

/-- `B = P.(4,t).S`. -/
theorem LeftSource.occ_child (s : LeftSource) :
    s.occ.child = s.P ++ 4 :: s.t :: s.S := by
  unfold Occ.child
  rw [offset_left _ (leftTag_ne_finalRight s.S)]
  simp only [LeftSource.occ, splitAt_append]
  simp

/-- Row 1 is charged on `A`, the parent of the source. -/
theorem LeftSource.row1Label_parent (s : LeftSource) :
    s.row1Label.parent = s.occ.parent := rfl

/-- The edge of row 1 is `A → C`, `C = P.(2,t+2).S`. -/
theorem LeftSource.row1Label_child (s : LeftSource) :
    s.row1Label.child = s.P ++ 2 :: (s.t + 2) :: s.S := by
  unfold Occ.child
  rw [offset_left _ (leftTag_ne_finalRight s.S)]
  simp only [LeftSource.row1Label, splitAt_append]
  simp

/-- Row 2 is charged on `C`, the child of the label of row 1. -/
theorem LeftSource.row2Label_parent (s : LeftSource) :
    s.row2Label.parent = s.row1Label.child := by
  rw [LeftSource.row1Label_child]; rfl

/-- The edge of row 2 is `C → D`, `D = P.(2,2,t).S`. -/
theorem LeftSource.row2Label_child (s : LeftSource) :
    s.row2Label.child = s.P ++ 2 :: 2 :: s.t :: s.S := by
  unfold Occ.child
  rw [offset_left _ (leftTag_ne_finalRight s.S)]
  simp only [LeftSource.row2Label, splitAt_append_succ]
  simp

/-- `B → D` is the split `4 ↦ (2,2)`: the two paths of the square have the
same end. -/
theorem LeftSource.square_closes (s : LeftSource) :
    splitAt s.occ.child s.P.length 2 = s.row2Label.child := by
  rw [LeftSource.occ_child, LeftSource.row2Label_child, splitAt_append]

/-- The edge of row 3 is `A → C` with `C = P.(t+2,2) = X_0`. -/
theorem Source.row3Label_child (s : Source) : s.row3Label.child = sqX s.P s.t := by
  simp only [Source.row3Label, Occ.child, Occ.offset, getD_append_length, splitAt_append, sqX]
  have h1 : s.t + 4 - 2 = s.t + 2 := by omega
  have h2 : s.t + 4 - (s.t + 2) = 2 := by omega
  rw [h1, h2]

theorem Source.row3Label_parent (s : Source) : s.row3Label.parent = s.occ.parent := rfl

/-! ### The sources and the labels are selected occurrences -/

/-- The left sources at size `N` are exactly the selected nonfinal and
final-left `F_4` occurrences on compositions of `N`. -/
theorem selected_left_F4_iff (N : ℕ) (o : Occ) :
    (o.Selected ∧ o.s = 4 ∧ o.tag ≠ .finalRight ∧ o.parent.sum = N) ↔
      ∃ s : LeftSource, s.Valid N ∧ s.occ = o := by
  constructor
  · rintro ⟨⟨-, hsupp, hblk, hpos⟩, hs, htag, hsum⟩
    obtain ⟨s, tag, c, i⟩ := o
    simp only at hs htag hsum hsupp hblk hpos
    subst hs
    have hi : i < c.length := by
      cases tag <;> simp only at hpos <;> omega
    have hd := decomp_at c i hi
    have hlen : (c.take i).length = i := length_take_of_lt c i (by omega)
    have h4 : c.getD i 0 - 4 + 4 = c.getD i 0 := by omega
    have htag' : leftTag (c.drop (i + 1)) = tag := by
      cases tag with
      | nonfinal =>
        simp only at hpos
        exact leftTag_of_ne (by
          intro h
          have := congrArg List.length h
          simp at this
          omega)
      | finalLeft =>
        simp only at hpos
        rw [List.drop_eq_nil_of_le (by omega)]
        rfl
      | finalRight => exact absurd rfl htag
    refine ⟨⟨c.take i, c.getD i 0 - 4, c.drop (i + 1)⟩, ⟨?_, ?_, by simp only; omega, ?_⟩, ?_⟩
    · exact fun m hm => hsupp m (List.take_subset i c hm)
    · exact fun m hm => hsupp m (List.drop_subset (i + 1) c hm)
    · have h2 : c.sum = (c.take i).sum + c.getD i 0 + (c.drop (i + 1)).sum := by
        conv_lhs => rw [hd]
        exact sum_decomp _ _ _
      simp only
      omega
    · simp only [LeftSource.occ, Occ.mk.injEq, true_and, hlen, and_true, h4, htag']
      exact hd.symm
  · rintro ⟨⟨P, t, S⟩, ⟨hP, hS, ht, hsum⟩, rfl⟩
    simp only at hP hS ht hsum
    refine ⟨⟨by simp [LeftSource.occ], ?_, ?_, ?_⟩, rfl, leftTag_ne_finalRight S, ?_⟩
    · exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, hS⟩⟩
    · simp only [LeftSource.occ, getD_append_length]
      omega
    · exact leftTag_position P S (t + 4)
    · simp only [LeftSource.occ]
      rw [sum_decomp]
      omega

theorem LeftSource.row1Label_selected (s : LeftSource) (N : ℕ) (h : s.Valid N) :
    s.row1Label.Selected := by
  obtain ⟨hP, hS, ht, -⟩ := h
  refine ⟨by simp [LeftSource.row1Label], ?_, ?_, leftTag_position s.P s.S (s.t + 4)⟩
  · exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, hS⟩⟩
  · simp only [LeftSource.row1Label, getD_append_length]
    omega

theorem LeftSource.row2Label_selected (s : LeftSource) (N : ℕ) (h : s.Valid N) :
    s.row2Label.Selected := by
  obtain ⟨hP, hS, ht, -⟩ := h
  have hg : (s.P ++ 2 :: (s.t + 2) :: s.S).getD (s.P.length + 1) 0 = s.t + 2 := by
    simp
  refine ⟨by simp [LeftSource.row2Label], ?_, ?_, ?_⟩
  · exact supp_append.2 ⟨hP, supp_cons.2 ⟨le_refl 2, supp_cons.2 ⟨by omega, hS⟩⟩⟩
  · simp only [LeftSource.row2Label, hg]
    omega
  · simp only [LeftSource.row2Label]
    unfold leftTag
    split_ifs with h
    · simp [h]
    · have : 0 < s.S.length := List.length_pos_iff.2 h
      simp only [List.length_append, List.length_cons]
      omega

theorem Source.row3Label_selected (s : Source) (N : ℕ) (h : s.Valid N) :
    s.row3Label.Selected := by
  obtain ⟨hP, ht, -⟩ := h
  refine ⟨by simp [Source.row3Label], ?_, ?_, by simp [Source.row3Label]⟩
  · exact supp_append.2 ⟨hP, supp_cons.2 ⟨by omega, fun m hm => by simp at hm⟩⟩
  · simp only [Source.row3Label, getD_append_length]
    omega

/-! ### At most one origin -/

theorem LeftSource.row1Label_injective : Function.Injective LeftSource.row1Label := by
  rintro ⟨P, t, S⟩ ⟨P', t', S'⟩ h
  simp only [LeftSource.row1Label, Occ.mk.injEq, true_and] at h
  obtain ⟨-, h1, h2⟩ := h
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq] at h3
  obtain ⟨rfl, h4, rfl⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

theorem LeftSource.row2Label_injective : Function.Injective LeftSource.row2Label := by
  rintro ⟨P, t, S⟩ ⟨P', t', S'⟩ h
  simp only [LeftSource.row2Label, Occ.mk.injEq, true_and] at h
  obtain ⟨-, h1, h2⟩ := h
  have h3 := List.append_inj h1 (by omega)
  simp only [List.cons.injEq, true_and] at h3
  obtain ⟨rfl, h4, rfl⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

theorem Source.row3Label_injective : Function.Injective Source.row3Label := by
  rintro ⟨P, t⟩ ⟨P', t'⟩ h
  simp only [Source.row3Label, Occ.mk.injEq, true_and] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq, and_true] at h3
  obtain ⟨rfl, h4⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

/-- **Rows 1–3, multiplicity.**  A left source charges the label `o` in
row 1 once if `o` is its row-1 label and not at all otherwise. -/
theorem LeftSource.count_row1 (s : LeftSource) (o : Occ) :
    s.charges.count ⟨.row1, o⟩ = if s.row1Label = o then 1 else 0 := by
  by_cases h : s.row1Label = o
  · subst h; simp [LeftSource.charges]
  · simp [LeftSource.charges, h]

theorem LeftSource.count_row2 (s : LeftSource) (o : Occ) :
    s.charges.count ⟨.row2, o⟩ = if s.row2Label = o then 1 else 0 := by
  by_cases h : s.row2Label = o
  · subst h; simp [LeftSource.charges]
  · simp [LeftSource.charges, h]

theorem Source.count_row3 (s : Source) (o : Occ) :
    s.topCharges.count ⟨.row3, o⟩ = if s.row3Label = o then 1 else 0 := by
  by_cases h : s.row3Label = o
  · subst h; simp [Source.topCharges]
  · simp [Source.topCharges, h]

/-- A left source makes no charge of row 3, and a final-right source makes
no charge of rows 1 and 2 in its initial square. -/
theorem LeftSource.count_row3 (s : LeftSource) (o : Occ) :
    s.charges.count ⟨.row3, o⟩ = 0 := by
  simp [LeftSource.charges]

theorem Source.count_row1_row2 (s : Source) (o : Occ) :
    s.topCharges.count ⟨.row1, o⟩ = 0 ∧ s.topCharges.count ⟨.row2, o⟩ = 0 := by
  simp [Source.topCharges]

/-! ### When an origin exists -/

/-- **Row 1.**  An occurrence is the row-1 label of a left source at size
`N` exactly when it is a selected left `F_2` occurrence, nonfinal or final,
of a block at least 6. -/
theorem row1_origin_exists_iff (N : ℕ) (o : Occ) :
    (∃ s : LeftSource, s.Valid N ∧ s.row1Label = o) ↔
      o.Selected ∧ o.s = 2 ∧ o.tag ≠ .finalRight ∧ 6 ≤ o.parent.getD o.idx 0 ∧
        o.parent.sum = N := by
  constructor
  · rintro ⟨s, hv, rfl⟩
    refine ⟨s.row1Label_selected N hv, rfl, leftTag_ne_finalRight s.S, ?_, ?_⟩
    · simp only [LeftSource.row1Label, getD_append_length]
      have := hv.2.2.1
      omega
    · simp only [LeftSource.row1Label]
      rw [sum_decomp]
      exact hv.2.2.2
  · rintro ⟨hsel, hs, htag, h6, hsum⟩
    -- the `F_4` occurrence on the same block with the same tag is selected
    have h4 : (⟨4, o.tag, o.parent, o.idx⟩ : Occ).Selected :=
      ⟨by simp, hsel.2.1, by simpa using h6, hsel.2.2.2⟩
    obtain ⟨s, hv, hocc⟩ := (selected_left_F4_iff N ⟨4, o.tag, o.parent, o.idx⟩).1
      ⟨h4, rfl, htag, hsum⟩
    refine ⟨s, hv, ?_⟩
    simp only [LeftSource.occ, Occ.mk.injEq, true_and] at hocc
    obtain ⟨o_s, o_tag, o_parent, o_idx⟩ := o
    simp only at hs hocc
    subst hs
    simp only [LeftSource.row1Label, Occ.mk.injEq, true_and]
    exact hocc

/-- **Row 3.**  An occurrence is the row-3 label of a final-right source at
size `N` exactly when it is a selected right `F_2` occurrence of a final
block at least 6. -/
theorem row3_origin_exists_iff (N : ℕ) (o : Occ) :
    (∃ s : Source, s.Valid N ∧ s.row3Label = o) ↔
      o.Selected ∧ o.s = 2 ∧ o.tag = .finalRight ∧ 6 ≤ o.parent.getD o.idx 0 ∧
        o.parent.sum = N := by
  constructor
  · rintro ⟨s, hv, rfl⟩
    refine ⟨s.row3Label_selected N hv, rfl, rfl, ?_, ?_⟩
    · simp only [Source.row3Label, getD_append_length]
      have := hv.2.1
      omega
    · simp only [Source.row3Label, List.sum_append, List.sum_cons, List.sum_nil]
      have := hv.2.2
      omega
  · rintro ⟨hsel, hs, htag, h6, hsum⟩
    obtain ⟨o_s, o_tag, o_parent, o_idx⟩ := o
    simp only at hs htag h6 hsum
    subst hs htag
    have h4 : (⟨4, .finalRight, o_parent, o_idx⟩ : Occ).Selected :=
      ⟨by simp, hsel.2.1, by simpa using h6, hsel.2.2.2⟩
    obtain ⟨s, hv, hocc⟩ := (selected_finalRight_F4_iff N ⟨4, .finalRight, o_parent, o_idx⟩).1
      ⟨h4, rfl, rfl, hsum⟩
    refine ⟨s, hv, ?_⟩
    simp only [Source.occ, Occ.mk.injEq, true_and] at hocc
    simp only [Source.row3Label, Occ.mk.injEq, true_and]
    exact hocc

/-- **Row 2.**  An occurrence is the row-2 label of a left source at size
`N` exactly when it is a selected left `F_2` occurrence, nonfinal or final,
whose block is immediately preceded by a block equal to 2.  The origin is
recovered by merging the block with that 2. -/
theorem row2_origin_exists_iff (N : ℕ) (o : Occ) :
    (∃ s : LeftSource, s.Valid N ∧ s.row2Label = o) ↔
      o.Selected ∧ o.s = 2 ∧ o.tag ≠ .finalRight ∧ 1 ≤ o.idx ∧
        o.parent.getD (o.idx - 1) 0 = 2 ∧ o.parent.sum = N := by
  constructor
  · rintro ⟨s, hv, rfl⟩
    refine ⟨s.row2Label_selected N hv, rfl, leftTag_ne_finalRight s.S, by simp [LeftSource.row2Label],
      ?_, ?_⟩
    · simp only [LeftSource.row2Label, Nat.add_sub_cancel, getD_append_length]
    · simp only [LeftSource.row2Label]
      rw [sum_decomp]
      have := hv.2.2.2
      simp only [List.sum_cons]
      omega
  · rintro ⟨⟨-, hsupp, hblk, hpos⟩, hs, htag, hidx, hprev, hsum⟩
    obtain ⟨o_s, tag, c, i⟩ := o
    simp only at hs htag hidx hprev hsum hsupp hblk hpos
    subst hs
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hprev
    have hi : k + 1 < c.length := by
      cases tag <;> simp only at hpos <;> omega
    have hd := decomp_at2 c k hi
    rw [hprev] at hd
    have hlen : (c.take k).length = k := length_take_of_lt c k (by omega)
    have h2 : c.getD (k + 1) 0 - 2 + 2 = c.getD (k + 1) 0 := by omega
    have htag' : leftTag (c.drop (k + 2)) = tag := by
      cases tag with
      | nonfinal =>
        simp only at hpos
        exact leftTag_of_ne (by
          intro h
          have := congrArg List.length h
          simp at this
          omega)
      | finalLeft =>
        simp only at hpos
        rw [List.drop_eq_nil_of_le (by omega)]
        rfl
      | finalRight => exact absurd rfl htag
    refine ⟨⟨c.take k, c.getD (k + 1) 0 - 2, c.drop (k + 2)⟩,
      ⟨?_, ?_, by simp only; omega, ?_⟩, ?_⟩
    · exact fun m hm => hsupp m (List.take_subset k c hm)
    · exact fun m hm => hsupp m (List.drop_subset (k + 2) c hm)
    · have h3 : c.sum = (c.take k).sum + 2 + (c.getD (k + 1) 0 + (c.drop (k + 2)).sum) := by
        conv_lhs => rw [hd]
        rw [sum_decomp, List.sum_cons]
      simp only
      omega
    · simp only [LeftSource.row2Label, Occ.mk.injEq, true_and, hlen, and_true, h2, htag']
      exact hd.symm

/-- **Rows 1–3: the charged occurrence and the row determine the origin.** -/
theorem top_origin_unique :
    (∀ s s' : LeftSource, s.row1Label = s'.row1Label → s = s') ∧
    (∀ s s' : LeftSource, s.row2Label = s'.row2Label → s = s') ∧
    (∀ s s' : Source, s.row3Label = s'.row3Label → s = s') :=
  ⟨fun _ _ h => LeftSource.row1Label_injective h,
    fun _ _ h => LeftSource.row2Label_injective h,
    fun _ _ h => Source.row3Label_injective h⟩

/-! ### Diagnostic examples -/

section Examples

/-! A nonfinal block 6: `A = (6,2)`, `B = (4,2,2)`, `C = (2,4,2)`,
`D = (2,2,2,2)`. -/

example : (⟨[], 2, [2]⟩ : LeftSource).occ = ⟨4, .nonfinal, [6, 2], 0⟩ := by decide

example : (⟨[], 2, [2]⟩ : LeftSource).occ.child = [4, 2, 2] := by decide

example : (⟨[], 2, [2]⟩ : LeftSource).row1Label = ⟨2, .nonfinal, [6, 2], 0⟩ ∧
    (⟨[], 2, [2]⟩ : LeftSource).row1Label.child = [2, 4, 2] := by decide

example : (⟨[], 2, [2]⟩ : LeftSource).row2Label = ⟨2, .nonfinal, [2, 4, 2], 1⟩ ∧
    (⟨[], 2, [2]⟩ : LeftSource).row2Label.child = [2, 2, 2, 2] := by decide

/-! The label `(2,4,2) → (2,2,2,2)` on the block 4 is also the row-5 label
of the cascade at `Q = (2)`, `y = 2`: one occurrence, charges of two types. -/

example : (⟨[], 2, [2]⟩ : LeftSource).row2Label = (chargeAt [2] 2).label := by decide

/-! A final block 8: the final-left label is a left source and the
final-right label is a cascade source; the two charge different `F_2`
occurrences of `(8)`. -/

example : (⟨[], 4, []⟩ : LeftSource).occ = (⟨[], 4⟩ : Source).leftOcc := by decide

example : (⟨[], 4, []⟩ : LeftSource).row1Label = ⟨2, .finalLeft, [8], 0⟩ ∧
    (⟨[], 4⟩ : Source).row3Label = ⟨2, .finalRight, [8], 0⟩ := by decide

example : (⟨[], 4, []⟩ : LeftSource).row1Label.child = [2, 6] ∧
    (⟨[], 4⟩ : Source).row3Label.child = [6, 2] := by decide

/-! A block 5 has no row-1 origin: the block must be at least 6. -/

example (N : ℕ) : ¬ ∃ s : LeftSource, s.Valid N ∧ s.row1Label = ⟨2, .nonfinal, [5, 2], 0⟩ := by
  rw [row1_origin_exists_iff]
  rintro ⟨-, -, -, h, -⟩
  revert h
  decide

/-! The block 5 of `(2,5,2)` is preceded by a 2 and has the row-2 origin
on `(7,2)`. -/

example : (⟨[], 3, [2]⟩ : LeftSource).row2Label = ⟨2, .nonfinal, [2, 5, 2], 1⟩ ∧
    (⟨[], 3, [2]⟩ : LeftSource).occ.parent = [7, 2] := by decide

end Examples

end K4
end ChowCone
