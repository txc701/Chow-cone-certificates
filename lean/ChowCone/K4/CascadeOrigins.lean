/-
Origins and multiplicities of the cascade charges (rows 4–6 of Table 1).

Manuscript of 21 November 2026: Section 7 (zero-divergence rerouting), the
final-right square (31) `A = P.(t+4), B = P.(t,4), C = P.(t+2,2),
D = P.(t,2,2)`, the cascade vertices (32) `X_j, Y_j, Z_j, W_j`, the cascade
square (33), the statement about origins in Lemma 8.1, and rows 4–6 of
Table 1.  The correspondence is tabulated in `K4_LEAN_CORRESPONDENCE.md`.

Scope.  This file verifies which final-right `F_4` origins charge which
labels in rows 4–6, with multiplicity.  It does not formalize row 3 (the
initial final-right `F_2` charge), rows 1–2, the sizes of the charges, the
collision or capacity inequalities, the divergence of the signed flow, or
the matroid bridge.

Compositions are lists of natural numbers, as in the `k = 2` files; `Supp`,
`splitAt` and `indN` are the definitions of `ChowCone.Basic` and
`ChowCone.Flow`.
-/
import ChowCone.Flow

namespace ChowCone
namespace K4

/-! ### Tagged occurrences of the primitive move multisets `F_s` -/

/-- Which of the three kinds of selected move an occurrence is
(manuscript Section 6): on a nonfinal block `m ↦ (s, m-s)`; on a final
block either `m ↦ (s, m-s)` (left) or `m ↦ (m-s, s)` (right). -/
inductive Tag
  | nonfinal
  | finalLeft
  | finalRight
  deriving DecidableEq, Repr

/-- A tagged occurrence of `F_s`: the primitive index `s`, the tag, the
parent composition and the index of the affected block.  Two occurrences
with different tags are different even when they are the same edge. -/
structure Occ where
  s : ℕ
  tag : Tag
  parent : List ℕ
  idx : ℕ
  deriving DecidableEq, Repr

/-- The split offset of an occurrence. -/
def Occ.offset (o : Occ) : ℕ :=
  match o.tag with
  | .finalRight => o.parent.getD o.idx 0 - o.s
  | _ => o.s

/-- The child composition; `(o.parent, o.child)` is the edge of `o`. -/
def Occ.child (o : Occ) : List ℕ := splitAt o.parent o.idx o.offset

/-- `o` is a selected occurrence of `F_s` (manuscript Section 6):
`s ∈ {2,3,4}`, the parent is a support composition, the affected block is
at least `s + 2`, and the tag agrees with the position of the block. -/
def Occ.Selected (o : Occ) : Prop :=
  (2 ≤ o.s ∧ o.s ≤ 4) ∧ Supp o.parent ∧ o.s + 2 ≤ o.parent.getD o.idx 0 ∧
    match o.tag with
    | .nonfinal => o.idx + 1 < o.parent.length
    | _ => o.idx + 1 = o.parent.length

/-! ### List helpers -/

lemma getD_append_length (Q S : List ℕ) (m : ℕ) :
    (Q ++ m :: S).getD Q.length 0 = m := by
  induction Q with
  | nil => rfl
  | cons a l ih => simp

lemma take_append_length' (Q S : List ℕ) : (Q ++ S).take Q.length = Q := by
  induction Q with
  | nil => simp
  | cons a l ih => simp

lemma drop_append_length_succ' (Q S : List ℕ) (m : ℕ) :
    (Q ++ m :: S).drop (Q.length + 1) = S := by
  induction Q with
  | nil => simp
  | cons a l ih => simp

/-- Splitting the block `m` that follows the prefix `Q`. -/
lemma splitAt_append (Q S : List ℕ) (m p : ℕ) :
    splitAt (Q ++ m :: S) Q.length p = Q ++ p :: (m - p) :: S := by
  unfold splitAt
  rw [take_append_length', getD_append_length, drop_append_length_succ']

lemma supp_append {Q S : List ℕ} : Supp (Q ++ S) ↔ Supp Q ∧ Supp S := by
  unfold Supp
  constructor
  · intro h
    exact ⟨fun m hm => h m (List.mem_append.2 (Or.inl hm)),
      fun m hm => h m (List.mem_append.2 (Or.inr hm))⟩
  · rintro ⟨h1, h2⟩ m hm
    rcases List.mem_append.1 hm with h | h
    · exact h1 m h
    · exact h2 m h

/-! ### Sources: tagged final-right `F_4` occurrences -/

/-- A source is the final-right `F_4` occurrence on the last block of
`P.(t+4)`.  It is recorded by the prefix `P` and the parameter `t`. -/
structure Source where
  P : List ℕ
  t : ℕ
  deriving DecidableEq, Repr

/-- The source lives at total size `N`: `P` is a support composition (it
may be empty), `t ≥ 2` and `sum P + t + 4 = N`. -/
def Source.Valid (N : ℕ) (s : Source) : Prop :=
  Supp s.P ∧ 2 ≤ s.t ∧ s.P.sum + s.t + 4 = N

/-- The final-right `F_4` occurrence of a source. -/
def Source.occ (s : Source) : Occ :=
  ⟨4, .finalRight, s.P ++ [s.t + 4], s.P.length⟩

/-- The final-left `F_4` occurrence on the same block.  It is not a source
of a cascade. -/
def Source.leftOcc (s : Source) : Occ :=
  ⟨4, .finalLeft, s.P ++ [s.t + 4], s.P.length⟩

theorem Source.occ_injective : Function.Injective Source.occ := by
  rintro ⟨P, t⟩ ⟨P', t'⟩ h
  simp only [Source.occ, Occ.mk.injEq, true_and] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq, and_true] at h3
  obtain ⟨rfl, h4⟩ := h3
  have : t = t' := by omega
  subst this
  rfl

/-- The sources at size `N` are exactly the selected final-right `F_4`
occurrences on compositions of `N`. -/
theorem selected_finalRight_F4_iff (N : ℕ) (o : Occ) :
    (o.Selected ∧ o.s = 4 ∧ o.tag = .finalRight ∧ o.parent.sum = N) ↔
      ∃ s : Source, s.Valid N ∧ s.occ = o := by
  constructor
  · rintro ⟨⟨-, hsupp, hblk, hpos⟩, hs, htag, hsum⟩
    obtain ⟨s, tag, c, i⟩ := o
    simp only at hs htag hsum hsupp hblk hpos
    subst hs htag
    simp only at hpos
    have hi : i < c.length := by omega
    have hd := decomp_at c i hi
    have hdrop : c.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop] at hd
    refine ⟨⟨c.take i, c.getD i 0 - 4⟩, ⟨?_, by simp only; omega, ?_⟩, ?_⟩
    · intro m hm
      exact hsupp m (List.take_subset i c hm)
    · have h2 : c.sum = (c.take i).sum + c.getD i 0 := by
        conv_lhs => rw [hd]
        simp
      simp only
      omega
    · have hlen : (c.take i).length = i := length_take_of_lt c i (by omega)
      have h4 : c.getD i 0 - 4 + 4 = c.getD i 0 := by omega
      simp only [Source.occ, Occ.mk.injEq, true_and, hlen, and_true, h4]
      exact hd.symm
  · rintro ⟨⟨P, t⟩, ⟨hP, ht, hsum⟩, rfl⟩
    simp only at hP ht hsum
    refine ⟨⟨by simp [Source.occ], ?_, ?_, ?_⟩, rfl, rfl, ?_⟩
    · simp only [Source.occ]
      exact supp_append.2 ⟨hP, by intro m hm; simp at hm; omega⟩
    · simp only [Source.occ, getD_append_length]
      omega
    · simp [Source.occ]
    · simp only [Source.occ, List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- The edge of a source is `A = P.(t+4) → B = P.(t,4)`. -/
theorem Source.occ_child (s : Source) : s.occ.child = s.P ++ [s.t, 4] := by
  simp only [Source.occ, Occ.child, Occ.offset, getD_append_length, splitAt_append]
  simp

theorem Source.leftOcc_child (s : Source) : s.leftOcc.child = s.P ++ [4, s.t] := by
  simp only [Source.leftOcc, Occ.child, Occ.offset, splitAt_append]
  simp

/-- The final-left label is a different occurrence. -/
theorem Source.leftOcc_ne_occ (s : Source) : s.leftOcc ≠ s.occ := by
  simp [Source.leftOcc, Source.occ]

/-- The two labels determine the same edge exactly when `t = 4`. -/
theorem Source.leftOcc_child_eq_iff (s : Source) :
    s.leftOcc.child = s.occ.child ↔ s.t = 4 := by
  rw [Source.leftOcc_child, Source.occ_child]
  constructor
  · intro h
    have := List.append_cancel_left h
    simp only [List.cons.injEq, and_true] at this
    omega
  · intro h
    rw [h]

/-! ### The path squares of Section 7 -/

/-- `X = Q.(y+2,2)`; for `Q = P.2^j`, `y = t - 2j` this is `X_j`. -/
def sqX (Q : List ℕ) (y : ℕ) : List ℕ := Q ++ [y + 2, 2]
/-- `Y = Q.(y,2,2)`. -/
def sqY (Q : List ℕ) (y : ℕ) : List ℕ := Q ++ [y, 2, 2]
/-- `Z = Q.2.(y,2)`. -/
def sqZ (Q : List ℕ) (y : ℕ) : List ℕ := Q ++ [2, y, 2]
/-- `W = Q.2.(y-2,2,2)`. -/
def sqW (Q : List ℕ) (y : ℕ) : List ℕ := Q ++ [2, y - 2, 2, 2]

/-- `X → Y` is the right peel `(y+2) ↦ (y,2)` of the penultimate block:
the edge that carries the debit at the state `(Q, y)`. -/
theorem sqY_eq_splitAt (Q : List ℕ) (y : ℕ) :
    sqY Q y = splitAt (sqX Q y) Q.length y := by
  simp only [sqX, sqY, splitAt_append]
  simp

/-- `X → Z` is the left peel `(y+2) ↦ (2,y)` of the penultimate block. -/
theorem sqZ_eq_splitAt (Q : List ℕ) (y : ℕ) :
    sqZ Q y = splitAt (sqX Q y) Q.length 2 := by
  simp only [sqX, sqZ, splitAt_append]
  simp

/-- `Y → W` is the left peel `y ↦ (2,y-2)`. -/
theorem sqW_eq_splitAt_sqY (Q : List ℕ) (y : ℕ) :
    sqW Q y = splitAt (sqY Q y) Q.length 2 := by
  simp only [sqY, sqW, splitAt_append]

/-- `Z → W` is the right peel `y ↦ (y-2,2)` of the penultimate block. -/
theorem sqW_eq_splitAt_sqZ (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    sqW Q y = splitAt (sqZ Q y) (Q.length + 1) (y - 2) := by
  have h := splitAt_append (Q ++ [2]) [2] y (y - 2)
  simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
    List.cons_append, List.nil_append] at h
  simp only [sqZ, sqW]
  rw [h]
  have : y - (y - 2) = 2 := by omega
  rw [this]

/-- `Z_j = X_{j+1}`: the next state is `(Q.2, y-2)`. -/
theorem sqZ_eq_sqX_next (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    sqZ Q y = sqX (Q ++ [2]) (y - 2) := by
  have : y - 2 + 2 = y := by omega
  simp [sqZ, sqX, this]

/-- `W_j = Y_{j+1}`. -/
theorem sqW_eq_sqY_next (Q : List ℕ) (y : ℕ) :
    sqW Q y = sqY (Q ++ [2]) (y - 2) := by
  simp [sqW, sqY]

/-- For `y ≥ 4` the consumed edge `X → Z` is not the debit edge `X → Y`. -/
theorem sqZ_ne_sqY (Q : List ℕ) (y : ℕ) (hy : 4 ≤ y) : sqZ Q y ≠ sqY Q y := by
  intro h
  have h2 := List.append_cancel_left h
  simp only [List.cons.injEq] at h2
  omega

/-- The initial final-right square: `C = P.(t+2,2)` is the right peel
`(t+4) ↦ (t+2,2)` of `A = P.(t+4)`, and `C = X_0`. -/
theorem sqX_eq_splitAt_source (s : Source) :
    sqX s.P s.t = splitAt s.occ.parent s.P.length (s.t + 2) := by
  simp only [Source.occ, sqX, splitAt_append]
  have : s.t + 4 - (s.t + 2) = 2 := by omega
  rw [this]

/-- `B → D`: `D = P.(t,2,2)` is the split `4 ↦ (2,2)` of the final block of
`B = P.(t,4)`, and `D = Y_0`. -/
theorem sqY_eq_splitAt_source_child (s : Source) :
    sqY s.P s.t = splitAt s.occ.child (s.P.length + 1) 2 := by
  rw [Source.occ_child]
  have h := splitAt_append (s.P ++ [s.t]) [] 4 2
  simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
    List.cons_append, List.nil_append] at h
  rw [h, sqY]

/-! ### Charges and the forward construction -/

/-- The three rows of Table 1 treated here. -/
inductive Row
  | row4
  | row5
  | row6
  deriving DecidableEq, Repr

/-- A charge: the row of Table 1 and the charged occurrence. -/
structure Charge where
  row : Row
  label : Occ
  deriving DecidableEq, Repr

/-- The `F_2` occurrence `(y+2) ↦ (2,y)` of the nonfinal block `y+2` of
`Q.(y+2,2)`. -/
def leftF2 (Q : List ℕ) (y : ℕ) : Occ := ⟨2, .nonfinal, Q ++ [y + 2, 2], Q.length⟩

/-- The `F_3` occurrence `5 ↦ (3,2)` of the nonfinal block `5` of `Q.(5,2)`. -/
def nonfinalF3 (Q : List ℕ) : Occ := ⟨3, .nonfinal, Q ++ [5, 2], Q.length⟩

/-- The forward construction, started at the state `(Q, y)`.

* `y ≥ 4`: one row-4 charge on the left `F_2` occurrence of the penultimate
  block of `Q.(y+2,2)`; continue at `(Q.2, y-2)`.
* `y = 2`: one row-5 charge on the `F_2` occurrence of `Q.(4,2)`; stop.
* `y = 3`: one row-6 charge on the `F_3` occurrence of `Q.(5,2)`; stop.

The list is ordered by stage, and its entries are counted with
multiplicity.  The values `y = 0, 1` do not occur for a source. -/
def cascade (Q : List ℕ) : ℕ → List Charge
  | 0 => []
  | 1 => []
  | 2 => [⟨.row5, leftF2 Q 2⟩]
  | 3 => [⟨.row6, nonfinalF3 Q⟩]
  | y + 4 => ⟨.row4, leftF2 Q (y + 4)⟩ :: cascade (Q ++ [2]) (y + 2)

/-- The charges made by a source, in the order of the stages. -/
def Source.trace (s : Source) : List Charge := cascade s.P s.t

/-- The applicable row and the charged label at `Q.(y+2,2)`: row 4 for
`y ≥ 4`, row 5 for `y = 2`, row 6 for `y = 3`. -/
def chargeAt (Q : List ℕ) (y : ℕ) : Charge :=
  if y = 3 then ⟨.row6, nonfinalF3 Q⟩
  else if y = 2 then ⟨.row5, leftF2 Q 2⟩
  else ⟨.row4, leftF2 Q y⟩

lemma chargeAt_label_parent (Q : List ℕ) (y : ℕ) :
    (chargeAt Q y).label.parent = Q ++ [y + 2, 2] := by
  unfold chargeAt
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rfl
  · rfl

lemma chargeAt_label_idx (Q : List ℕ) (y : ℕ) :
    (chargeAt Q y).label.idx = Q.length := by
  unfold chargeAt
  split_ifs <;> rfl

/-- The label determines `Q` and `y`. -/
theorem chargeAt_injective {Q Q' : List ℕ} {y y' : ℕ}
    (h : chargeAt Q y = chargeAt Q' y') : Q = Q' ∧ y = y' := by
  have h1 : Q ++ [y + 2, 2] = Q' ++ [y' + 2, 2] := by
    rw [← chargeAt_label_parent, ← chargeAt_label_parent, h]
  have h2 : Q.length = Q'.length := by
    rw [← chargeAt_label_idx Q y, ← chargeAt_label_idx Q' y', h]
  have h3 := List.append_inj h1 h2
  simp only [List.cons.injEq, and_true] at h3
  exact ⟨h3.1, by omega⟩

/-- The charged label is a selected occurrence. -/
theorem chargeAt_selected (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y) :
    (chargeAt Q y).label.Selected := by
  have hsupp : Supp (Q ++ [y + 2, 2]) :=
    supp_append.2 ⟨hQ, by intro m hm; simp at hm; omega⟩
  have hlen : Q.length + 1 < (Q ++ [y + 2, 2]).length := by simp
  unfold chargeAt
  split_ifs with h1 h2
  · subst h1
    exact ⟨by simp [nonfinalF3], hsupp, by simp [nonfinalF3], hlen⟩
  · subst h2
    exact ⟨by simp [leftF2], hsupp, by simp [leftF2], hlen⟩
  · refine ⟨by simp [leftF2], hsupp, ?_, hlen⟩
    simp only [leftF2, getD_append_length]
    omega

/-- For `y ≠ 3` the charged label is a selected move of the `k = 2`
peel-two flow: the indicator `indN` of `ChowCone.Flow` equals one. -/
theorem indN_leftF2 (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y) :
    indN (leftF2 Q y).parent (leftF2 Q y).idx 2 = 1 := by
  have hsupp : Supp (Q ++ [y + 2, 2]) :=
    supp_append.2 ⟨hQ, by intro m hm; simp at hm; omega⟩
  unfold indN
  rw [if_pos]
  refine ⟨hsupp, by simp [leftF2], rfl, ?_⟩
  simp only [leftF2, getD_append_length]
  omega

/-- Row 4: the consumed edge is `X → Z`. -/
theorem leftF2_child (Q : List ℕ) (y : ℕ) : (leftF2 Q y).child = sqZ Q y := by
  simp only [leftF2, Occ.child, Occ.offset, splitAt_append, sqZ]
  simp

/-- Row 5: at `y = 2` the consumed edge is also the debit edge `X → Y`. -/
theorem leftF2_two_child (Q : List ℕ) : (leftF2 Q 2).child = sqY Q 2 := by
  rw [leftF2_child]; rfl

/-- Row 6: the charged edge is the debit edge `X → Y` at `y = 3`, that is
`Q.(5,2) → Q.(3,2,2)`. -/
theorem nonfinalF3_child (Q : List ℕ) : (nonfinalF3 Q).child = sqY Q 3 := by
  simp only [nonfinalF3, Occ.child, Occ.offset, splitAt_append, sqY]

theorem chargeAt_parent_eq_sqX (Q : List ℕ) (y : ℕ) :
    (chargeAt Q y).label.parent = sqX Q y := chargeAt_label_parent Q y

/-! ### Step 1: the forward trace -/

/-- Stage `j` of the cascade started at `(P, t)` exists exactly when
`2j + 2 ≤ t`; it is then the charge at the prefix `P.2^j` with parameter
`t - 2j`. -/
theorem cascade_getElem? (P : List ℕ) (t j : ℕ) :
    (cascade P t)[j]? =
      if 2 * j + 2 ≤ t then some (chargeAt (P ++ List.replicate j 2) (t - 2 * j))
      else none := by
  induction P, t using cascade.induct generalizing j with
  | case1 => simp [cascade]
  | case2 => simp [cascade]
  | case3 =>
    cases j with
    | zero => simp [cascade, chargeAt]
    | succ j => simp [cascade]
  | case4 =>
    cases j with
    | zero => simp [cascade, chargeAt]
    | succ j =>
      rw [if_neg (by omega)]
      simp [cascade]
  | case5 P y ih =>
    cases j with
    | zero => simp [cascade, chargeAt]
    | succ j =>
      rw [cascade, List.getElem?_cons_succ, ih]
      have e1 : (2 * j + 2 ≤ y + 2) ↔ (2 * (j + 1) + 2 ≤ y + 4) := by omega
      have e2 : y + 2 - 2 * j = y + 4 - 2 * (j + 1) := by omega
      have e3 : P ++ [2] ++ List.replicate j 2 = P ++ List.replicate (j + 1) 2 := by
        simp [List.replicate_succ]
      simp only [e1, e2, e3]

/-- Additive form: stage `j` carries the charge `ch` exactly when
`t = y + 2j` for some `y ≥ 2` and `ch` is the charge at `P.2^j` with
parameter `y`. -/
theorem cascade_stage_iff (P : List ℕ) (t j : ℕ) (ch : Charge) :
    (cascade P t)[j]? = some ch ↔
      ∃ y, 2 ≤ y ∧ t = y + 2 * j ∧ ch = chargeAt (P ++ List.replicate j 2) y := by
  rw [cascade_getElem?]
  constructor
  · intro h
    split_ifs at h with h1
    exact ⟨t - 2 * j, by omega, by omega, (Option.some.inj h).symm⟩
  · rintro ⟨y, hy, rfl, rfl⟩
    rw [if_pos (by omega)]
    congr 2
    omega

/-- The number of stages is `⌊t/2⌋`. -/
theorem cascade_length (P : List ℕ) (t : ℕ) : (cascade P t).length = t / 2 := by
  induction P, t using cascade.induct with
  | case1 => simp [cascade]
  | case2 => simp [cascade]
  | case3 => simp [cascade]
  | case4 => simp [cascade]
  | case5 P y ih =>
    rw [cascade, List.length_cons, ih]
    omega

/-- A source charges each label at most once. -/
theorem cascade_nodup (P : List ℕ) (t : ℕ) : (cascade P t).Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj h
  have hi : i < (cascade P t).length := by omega
  rw [List.getElem?_eq_getElem hi] at h
  obtain ⟨y, -, -, e1⟩ := (cascade_stage_iff P t i _).1 (List.getElem?_eq_getElem hi)
  obtain ⟨y', -, -, e2⟩ := (cascade_stage_iff P t j _).1 h.symm
  have h3 := (chargeAt_injective (e1.symm.trans e2)).1
  have h4 := congrArg List.length h3
  simp at h4
  omega

/-! ### Step 2: suffixes of the trailing run of 2s -/

/-- The length `h` of the maximal trailing run of blocks equal to `2`. -/
def trailingTwos (Q : List ℕ) : ℕ := (Q.reverse.takeWhile (· = 2)).length

/-- The source recovered from the label at `Q.(y+2,2)` by deleting the
last `j` blocks of `Q` and replacing `y` by `y + 2j`. -/
def origin (Q : List ℕ) (y j : ℕ) : Source := ⟨Q.take (Q.length - j), y + 2 * j⟩

/-- All origins of the label at `Q.(y+2,2)`, for `j = 0, …, h`. -/
def origins (Q : List ℕ) (y : ℕ) : List Source :=
  (List.range (trailingTwos Q + 1)).map (origin Q y)

lemma replicate_two_le_trailingTwos (P : List ℕ) (j : ℕ) :
    j ≤ trailingTwos (P ++ List.replicate j 2) := by
  unfold trailingTwos
  rw [List.reverse_append, List.reverse_replicate,
    List.takeWhile_append_of_pos (by intro a ha; simp [List.eq_of_mem_replicate ha])]
  simp

lemma eq_append_replicate_trailingTwos (Q : List ℕ) :
    ∃ P, Q = P ++ List.replicate (trailingTwos Q) 2 := by
  refine ⟨(Q.reverse.dropWhile (· = 2)).reverse, ?_⟩
  have h1 : Q.reverse.takeWhile (· = 2) = List.replicate (trailingTwos Q) 2 := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    simpa using List.mem_takeWhile_imp hb
  have h2 := List.takeWhile_append_dropWhile (p := (· = 2)) (l := Q.reverse)
  rw [h1] at h2
  have h3 := congrArg List.reverse h2
  rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at h3
  exact h3.symm

/-- `Q = P.2^j` has a solution `P` exactly when `j ≤ h`, and then
`P` is `Q` without its last `j` blocks. -/
theorem eq_append_replicate_iff (Q P : List ℕ) (j : ℕ) :
    Q = P ++ List.replicate j 2 ↔ j ≤ trailingTwos Q ∧ P = Q.take (Q.length - j) := by
  constructor
  · rintro rfl
    refine ⟨replicate_two_le_trailingTwos P j, ?_⟩
    simp
  · rintro ⟨hj, rfl⟩
    obtain ⟨P₀, hP₀⟩ := eq_append_replicate_trailingTwos Q
    obtain ⟨k, hk⟩ : ∃ k, trailingTwos Q = k + j := ⟨trailingTwos Q - j, by omega⟩
    rw [hk, List.replicate_add, ← List.append_assoc] at hP₀
    have hlen : Q.length - j = (P₀ ++ List.replicate k 2).length := by
      rw [hP₀]; simp; omega
    rw [hlen]
    conv_lhs => rw [hP₀]
    conv_rhs => rw [hP₀, take_append_length']

/-- The solution `P` is unique. -/
theorem append_replicate_unique {P P' : List ℕ} {j : ℕ}
    (h : P ++ List.replicate j 2 = P' ++ List.replicate j 2) : P = P' :=
  List.append_cancel_right h

/-- `h` is the largest `j` such that `2^j` is a suffix of `Q`. -/
theorem exists_eq_append_replicate_iff (Q : List ℕ) (j : ℕ) :
    (∃ P, Q = P ++ List.replicate j 2) ↔ j ≤ trailingTwos Q := by
  constructor
  · rintro ⟨P, hP⟩
    exact ((eq_append_replicate_iff Q P j).1 hP).1
  · intro hj
    exact ⟨_, (eq_append_replicate_iff Q _ j).2 ⟨hj, rfl⟩⟩

/-! ### Step 3: the uniform target -/

/-- Stage `j` of the source `s` charges the label at `Q.(y+2,2)` exactly
when `j ≤ h` and `s` is the `j`-th origin. -/
theorem trace_stage_eq_chargeAt_iff (s : Source) (j : ℕ) (Q : List ℕ) (y : ℕ)
    (hy : 2 ≤ y) :
    s.trace[j]? = some (chargeAt Q y) ↔ j ≤ trailingTwos Q ∧ s = origin Q y j := by
  obtain ⟨P, t⟩ := s
  simp only [Source.trace]
  rw [cascade_stage_iff]
  constructor
  · rintro ⟨y', -, rfl, h⟩
    obtain ⟨hQ, rfl⟩ := chargeAt_injective h
    obtain ⟨hj, rfl⟩ := (eq_append_replicate_iff Q P j).1 hQ
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, h⟩
    simp only [origin, Source.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨y, hy, rfl, ?_⟩
    rw [← (eq_append_replicate_iff Q _ j).2 ⟨hj, rfl⟩]

/-- Forward/reverse inverse, forward direction: the `j`-th origin charges
the label at its stage `j`. -/
theorem origin_trace (Q : List ℕ) (y j : ℕ) (hy : 2 ≤ y) (hj : j ≤ trailingTwos Q) :
    (origin Q y j).trace[j]? = some (chargeAt Q y) :=
  (trace_stage_eq_chargeAt_iff _ j Q y hy).2 ⟨hj, rfl⟩

/-- Forward/reverse inverse, reverse direction: the origin of the label
charged at stage `j` of `(P, t)` is `(P, t)` again. -/
theorem origin_of_stage (P : List ℕ) (y j : ℕ) :
    origin (P ++ List.replicate j 2) y j = ⟨P, y + 2 * j⟩ := by
  simp [origin]

/-- The origins are sources at the same size `N`. -/
theorem origin_valid (N : ℕ) (Q : List ℕ) (y j : ℕ) (hQ : Supp Q) (hy : 2 ≤ y)
    (hN : Q.sum + y + 4 = N) (hj : j ≤ trailingTwos Q) : (origin Q y j).Valid N := by
  have hQ' := (eq_append_replicate_iff Q _ j).2 ⟨hj, rfl⟩
  refine ⟨?_, by simp only [origin]; omega, ?_⟩
  · intro m hm
    exact hQ m (List.take_subset _ Q hm)
  · have h2 : Q.sum = (Q.take (Q.length - j)).sum + 2 * j := by
      conv_lhs => rw [hQ']
      simp [List.sum_append, List.sum_replicate, Nat.mul_comm]
    simp only [origin]
    omega

/-- The origins for different `j` are different sources. -/
theorem origin_injective (Q : List ℕ) (y : ℕ) : Function.Injective (origin Q y) := by
  intro i j h
  simp only [origin, Source.mk.injEq] at h
  omega

theorem origins_nodup (Q : List ℕ) (y : ℕ) : (origins Q y).Nodup :=
  List.Nodup.map (origin_injective Q y) List.nodup_range

theorem origins_length (Q : List ℕ) (y : ℕ) : (origins Q y).length = trailingTwos Q + 1 := by
  simp [origins]

theorem mem_origins {Q : List ℕ} {y : ℕ} {s : Source} :
    s ∈ origins Q y ↔ ∃ j, j ≤ trailingTwos Q ∧ s = origin Q y j := by
  simp only [origins, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, rfl⟩

/-- A source charges the label at `Q.(y+2,2)` exactly when it is one of the
origins. -/
theorem chargeAt_mem_trace_iff (s : Source) (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    chargeAt Q y ∈ s.trace ↔ s ∈ origins Q y := by
  rw [List.mem_iff_getElem?, mem_origins]
  exact exists_congr fun j => trace_stage_eq_chargeAt_iff s j Q y hy

/-- **The uniform target, with multiplicity.**  For every source `s`, the
number of times `s` charges the label at `Q.(y+2,2)` equals the number of
times `s` occurs in the list of origins.  That list has no repetition and
`h + 1` entries, so each origin charges the label exactly once and no other
source charges it. -/
theorem count_trace_eq_count_origins (s : Source) (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    s.trace.count (chargeAt Q y) = (origins Q y).count s := by
  unfold Source.trace
  by_cases h : s ∈ origins Q y
  · rw [List.count_eq_one_of_mem (origins_nodup Q y) h,
      List.count_eq_one_of_mem (cascade_nodup s.P s.t)
        ((chargeAt_mem_trace_iff s Q y hy).2 h)]
  · rw [List.count_eq_zero_of_not_mem h, List.count_eq_zero_of_not_mem]
    exact fun h' => h ((chargeAt_mem_trace_iff s Q y hy).1 h')

/-- Total multiplicity over any finite family of sources that contains the
origins: the label is charged `h + 1` times. -/
theorem sum_count_trace (S : Finset Source) (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y)
    (hS : ∀ s ∈ origins Q y, s ∈ S) :
    ∑ s ∈ S, s.trace.count (chargeAt Q y) = trailingTwos Q + 1 := by
  have h1 : ∀ s ∈ S, s.trace.count (chargeAt Q y) = if s ∈ (origins Q y).toFinset then 1 else 0 := by
    intro s _
    rw [count_trace_eq_count_origins s Q y hy]
    by_cases h : s ∈ origins Q y
    · rw [List.count_eq_one_of_mem (origins_nodup Q y) h, if_pos (List.mem_toFinset.2 h)]
    · rw [List.count_eq_zero_of_not_mem h, if_neg (by simpa using h)]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : S ∩ (origins Q y).toFinset = (origins Q y).toFinset :=
    Finset.inter_eq_right.2 (fun s hs => hS s (List.mem_toFinset.1 hs))
  rw [h2, List.card_toFinset, List.dedup_eq_self.2 (origins_nodup Q y), origins_length]

/-- Every charge of every source is the charge at some `Q.(y+2,2)` with
`y ≥ 2`; in particular no other kind of label is charged. -/
theorem mem_trace_iff (s : Source) (ch : Charge) :
    ch ∈ s.trace ↔
      ∃ j y, 2 ≤ y ∧ s.t = y + 2 * j ∧ ch = chargeAt (s.P ++ List.replicate j 2) y := by
  rw [List.mem_iff_getElem?]
  exact exists_congr fun j => cascade_stage_iff s.P s.t j ch

/-- The `F_2` occurrence `5 ↦ (2,3)` of a nonfinal block `5` followed by
the final block `2` is never charged by a cascade, in any row. -/
theorem leftF2_three_not_charged (s : Source) (r : Row) (Q : List ℕ) :
    (⟨r, leftF2 Q 3⟩ : Charge) ∉ s.trace := by
  rw [mem_trace_iff]
  rintro ⟨j, y, hy, -, h⟩
  have hp := congrArg (fun c => c.label.parent) h
  have hi := congrArg (fun c => c.label.idx) h
  simp only [chargeAt_label_parent, chargeAt_label_idx] at hp hi
  simp only [leftF2] at hp hi
  have h3 := List.append_inj hp hi
  simp only [List.cons.injEq, and_true] at h3
  have hy3 : y = 3 := by omega
  subst hy3
  have hs := congrArg (fun c => c.label.s) h
  simp [chargeAt, leftF2, nonfinalF3] at hs

/-- Every charged label is an `F_2` or an `F_3` occurrence; no `F_4`
occurrence is charged, whatever edge it lies on. -/
theorem label_s_of_mem_trace (s : Source) (ch : Charge) (h : ch ∈ s.trace) :
    ch.label.s = 2 ∨ ch.label.s = 3 := by
  obtain ⟨j, y, -, -, rfl⟩ := (mem_trace_iff s ch).1 h
  unfold chargeAt
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- The row of the charge at `Q.(y+2,2)`. -/
theorem chargeAt_row (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    (chargeAt Q y).row = if 4 ≤ y then Row.row4 else if y = 2 then Row.row5 else Row.row6 := by
  unfold chargeAt
  split_ifs <;> first | rfl | omega

/-- The edge of the charged label: `X → Z` for `y ≥ 4` (row 4), and the
debit edge `X → Y` for `y = 2, 3` (rows 5 and 6). -/
theorem chargeAt_child (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    (chargeAt Q y).label.child = if 4 ≤ y then sqZ Q y else sqY Q y := by
  unfold chargeAt
  by_cases h4 : 4 ≤ y
  · rw [if_neg (by omega), if_neg (by omega), if_pos h4]
    exact leftF2_child Q y
  · rw [if_neg h4]
    by_cases h3 : y = 3
    · subst h3
      rw [if_pos rfl]
      exact nonfinalF3_child Q
    · have h2 : y = 2 := by omega
      subst h2
      rw [if_neg (by omega), if_pos rfl]
      exact leftF2_two_child Q

/-! ### The vertices in the indexing of the manuscript -/

/-- `X_j = P.2^j.(y+2,2)` with `y = t - 2j`. -/
def X (P : List ℕ) (t j : ℕ) : List ℕ := sqX (P ++ List.replicate j 2) (t - 2 * j)
/-- `Y_j = P.2^j.(y,2,2)`. -/
def Y (P : List ℕ) (t j : ℕ) : List ℕ := sqY (P ++ List.replicate j 2) (t - 2 * j)
/-- `Z_j = P.2^{j+1}.(y,2)`. -/
def Z (P : List ℕ) (t j : ℕ) : List ℕ := sqZ (P ++ List.replicate j 2) (t - 2 * j)
/-- `W_j = P.2^{j+1}.(y-2,2,2)`. -/
def W (P : List ℕ) (t j : ℕ) : List ℕ := sqW (P ++ List.replicate j 2) (t - 2 * j)

lemma append_replicate_succ (P : List ℕ) (j : ℕ) :
    P ++ List.replicate (j + 1) 2 = P ++ List.replicate j 2 ++ [2] := by
  rw [List.replicate_succ', List.append_assoc]

/-- `Z_j = X_{j+1}` when the stage `j` exists. -/
theorem Z_eq_X_succ (P : List ℕ) (t j : ℕ) (h : 2 * j + 2 ≤ t) : Z P t j = X P t (j + 1) := by
  unfold Z X
  rw [sqZ_eq_sqX_next _ _ (by omega), append_replicate_succ]
  congr 1

/-- `W_j = Y_{j+1}`. -/
theorem W_eq_Y_succ (P : List ℕ) (t j : ℕ) : W P t j = Y P t (j + 1) := by
  unfold W Y
  rw [sqW_eq_sqY_next, append_replicate_succ]
  congr 1

/-- The charge of stage `j` of the source `(P, t)` sits on `X_j`; its edge
is `X_j → Z_j` when `t - 2j ≥ 4` and `X_j → Y_j` at the terminal stage. -/
theorem stage_edge (s : Source) (j : ℕ) (ch : Charge) (h : s.trace[j]? = some ch) :
    ch.label.parent = X s.P s.t j ∧
      ch.label.child = if 4 ≤ s.t - 2 * j then Z s.P s.t j else Y s.P s.t j := by
  obtain ⟨y, hy, ht, rfl⟩ := (cascade_stage_iff s.P s.t j ch).1 h
  have e : s.t - 2 * j = y := by omega
  unfold X Y Z
  rw [e]
  exact ⟨chargeAt_parent_eq_sqX _ _, chargeAt_child _ _ hy⟩

/-! ### All sources at a given size -/

/-- There are finitely many sources at size `N`. -/
theorem validSources_finite (N : ℕ) : {s : Source | s.Valid N}.Finite := by
  have hfin : (Set.range fun c : Composition N => c.blocks).Finite := Set.finite_range _
  refine Set.Finite.of_finite_image (f := fun s : Source => s.occ.parent) (hfin.subset ?_) ?_
  · rintro c ⟨s, ⟨hP, ht, hsum⟩, rfl⟩
    refine ⟨⟨s.P ++ [s.t + 4], ?_, ?_⟩, rfl⟩
    · intro i hi
      rcases List.mem_append.1 hi with h | h
      · have := hP i h
        omega
      · simp at h
        omega
    · simp only [List.sum_append, List.sum_cons, List.sum_nil]
      omega
  · intro s _ s' _ h
    simp only [Source.occ] at h
    obtain ⟨P, t⟩ := s
    obtain ⟨P', t'⟩ := s'
    simp only at h
    have hlen : P.length = P'.length := by
      have := congrArg List.length h
      simpa using this
    have h3 := List.append_inj h hlen
    simp only [List.cons.injEq, and_true] at h3
    obtain ⟨rfl, h4⟩ := h3
    have : t = t' := by omega
    subst this
    rfl

/-- The total number of charges on the label at `Q.(y+2,2)`, summed over
all sources at size `N` and counted with multiplicity, is `h + 1`. -/
theorem total_multiplicity (N : ℕ) (Q : List ℕ) (y : ℕ) (hQ : Supp Q) (hy : 2 ≤ y)
    (hN : Q.sum + y + 4 = N) :
    ∑ s ∈ (validSources_finite N).toFinset, s.trace.count (chargeAt Q y) =
      trailingTwos Q + 1 := by
  refine sum_count_trace _ Q y hy fun s hs => ?_
  obtain ⟨j, hj, rfl⟩ := mem_origins.1 hs
  exact (Set.Finite.mem_toFinset _).2 (origin_valid N Q y j hQ hy hN hj)

/-- **Origins and multiplicities of the cascade charges, rows 4–6 of
Table 1.**  Fix a size `N` and the label at `Q.(y+2,2)` with `Q` a support
composition, `y ≥ 2` and `sum Q + y + 4 = N`.  Let `h` be the length of the
trailing run of 2s of `Q`.  Then:

1. the list of origins has no repetition and `h + 1` entries;
2. every origin is a source at size `N`;
3. the `j`-th origin charges the label at its stage `j`;
4. a stage `j` of a source `s` charges the label only if `j ≤ h` and `s` is
   the `j`-th origin;
5. every source charges the label as often as it occurs among the origins;
6. the total multiplicity over all sources at size `N` is `h + 1`.

The manuscript fixes `d ≥ 3` and `N = d + 2`.  The hypotheses force `N ≥ 6`,
that is `d ≥ 4`, so no condition on `d` is stated. -/
theorem cascade_charge_origins (N : ℕ) (Q : List ℕ) (y : ℕ)
    (hQ : Supp Q) (hy : 2 ≤ y) (hN : Q.sum + y + 4 = N) :
    ((origins Q y).Nodup ∧ (origins Q y).length = trailingTwos Q + 1) ∧
    (∀ s ∈ origins Q y, s.Valid N) ∧
    (∀ j, j ≤ trailingTwos Q → (origin Q y j).trace[j]? = some (chargeAt Q y)) ∧
    (∀ (s : Source) (j : ℕ), s.trace[j]? = some (chargeAt Q y) ↔
      j ≤ trailingTwos Q ∧ s = origin Q y j) ∧
    (∀ s : Source, s.trace.count (chargeAt Q y) = (origins Q y).count s) ∧
    ∑ s ∈ (validSources_finite N).toFinset, s.trace.count (chargeAt Q y) =
      trailingTwos Q + 1 := by
  refine ⟨⟨origins_nodup Q y, origins_length Q y⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := mem_origins.1 hs
    exact origin_valid _ Q y j hQ hy hN hj
  · exact fun j hj => origin_trace Q y j hy hj
  · exact fun s j => trace_stage_eq_chargeAt_iff s j Q y hy
  · exact fun s => count_trace_eq_count_origins s Q y hy
  · exact total_multiplicity _ Q y hQ hy hN

/-! ### Diagnostic examples -/

section Examples

/-- A source is never a final-left occurrence. -/
theorem Source.occ_ne_leftOcc (s s' : Source) : s.occ ≠ s'.leftOcc := by
  simp [Source.occ, Source.leftOcc]

/-! `Q = (2,2)`, `y = 2`: exactly the three final-right origins on
`(2,2,6)`, `(2,8)`, `(10)`; there is no `j = 3`. -/

example : trailingTwos [2, 2] = 2 := by decide

example : origins [2, 2] 2 = [⟨[2, 2], 2⟩, ⟨[2], 4⟩, ⟨[], 6⟩] := by decide

example : (origins [2, 2] 2).map (fun s => s.occ.parent) = [[2, 2, 6], [2, 8], [10]] := by
  decide

example : (⟨[2, 2], 2⟩ : Source).trace = [chargeAt [2, 2] 2] := by decide

example : (⟨[2], 4⟩ : Source).trace = [chargeAt [2] 4, chargeAt [2, 2] 2] := by decide

example : (⟨[], 6⟩ : Source).trace = [chargeAt [] 6, chargeAt [2] 4, chargeAt [2, 2] 2] := by
  decide

example (s : Source) : s.trace[3]? ≠ some (chargeAt [2, 2] 2) := by
  rw [Ne, trace_stage_eq_chargeAt_iff s 3 [2, 2] 2 (by norm_num)]
  rintro ⟨h, -⟩
  revert h
  decide

/-! `Q = ()`, `y = 3`: the charge is on the `F_3` label `(5,2) → (3,2,2)`,
not on the left `F_2` label `(5,2) → (2,3,2)`. -/

example : chargeAt [] 3 = ⟨.row6, ⟨3, .nonfinal, [5, 2], 0⟩⟩ := by decide

example : (chargeAt [] 3).label.child = [3, 2, 2] := by decide

example : leftF2 [] 3 = ⟨2, .nonfinal, [5, 2], 0⟩ ∧ (leftF2 [] 3).child = [2, 3, 2] := by
  decide

example (s : Source) (r : Row) : (⟨r, ⟨2, .nonfinal, [5, 2], 0⟩⟩ : Charge) ∉ s.trace :=
  leftF2_three_not_charged s r []

/-! `Q = ()`, `y = 4`: `(8) → (4,4)` carries two labels and only the
final-right one is a source.  The intermediate debit edge
`(6,2) → (4,2,2)` is also the edge of a nonfinal `F_4` occurrence; the
charge is not duplicated. -/

example : (⟨[], 4⟩ : Source).occ = ⟨4, .finalRight, [8], 0⟩ ∧
    (⟨[], 4⟩ : Source).leftOcc = ⟨4, .finalLeft, [8], 0⟩ := by decide

example : (⟨[], 4⟩ : Source).occ.child = [4, 4] ∧ (⟨[], 4⟩ : Source).leftOcc.child = [4, 4] := by
  decide

example (s : Source) : s.occ ≠ (⟨4, .finalLeft, [8], 0⟩ : Occ) :=
  Source.occ_ne_leftOcc s ⟨[], 4⟩

example : origins [] 4 = [⟨[], 4⟩] := by decide

example : (⟨[], 4⟩ : Source).trace =
    [⟨.row4, ⟨2, .nonfinal, [6, 2], 0⟩⟩, ⟨.row5, ⟨2, .nonfinal, [2, 4, 2], 1⟩⟩] := by decide

example : sqX [] 4 = [6, 2] ∧ sqY [] 4 = [4, 2, 2] ∧
    (⟨4, .nonfinal, [6, 2], 0⟩ : Occ).child = [4, 2, 2] := by decide

example : (⟨4, .nonfinal, [6, 2], 0⟩ : Occ).Selected :=
  ⟨by decide, by decide, by decide, by decide⟩

example : (⟨[], 4⟩ : Source).trace.count (chargeAt [] 4) = 1 := by decide

example : ∀ ch ∈ (⟨[], 4⟩ : Source).trace, ch.label ≠ ⟨4, .nonfinal, [6, 2], 0⟩ := by decide

/-! A prefix with an earlier 2 that is not trailing: `Q = (2,3)`, `y = 2`
has `h = 0`. -/

example : trailingTwos [2, 3] = 0 := by decide

example : origins [2, 3] 2 = [⟨[2, 3], 2⟩] := by decide

end Examples

end K4
end ChowCone
