/-
Evaluation of `f_d` on an edge: the cascade of one source telescopes, and
`f_d` is `f_0` plus nine sums, one for each role an edge can play in a
path square.

Manuscript of 21 November 2026: Section 7 (the recursive transfer of the
debt) and Section 8, the paragraph before Table 1: "At each stage with
`y ≥ 4`, the current debit on `X_j → Y_j` is `-R`, and the square (33)
contributes `+R` on that same edge.  The two terms cancel."

Scope.  This file contains no inequality.  It rewrites `f_d`; the bounds
are in `ChowCone.K4.Nonnegativity`.
-/
import ChowCone.K4.Rerouting

namespace ChowCone
namespace K4

open Finset

/-! ### Unit flows, pointwise -/

lemma edgeUnit_apply (e : PEdge) (c : List ℕ) (i p : ℕ) :
    edgeUnit e c i p = if e = ⟨c, i, p⟩ then 1 else 0 := by
  obtain ⟨c', i', p'⟩ := e
  simp only [edgeUnit, PEdge.mk.injEq]
  exact if_congr ⟨fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩,
    fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩ rfl rfl

lemma edgeUnit_nonneg (e : PEdge) (c : List ℕ) (i p : ℕ) : 0 ≤ edgeUnit e c i p := by
  rw [edgeUnit_apply]
  split_ifs <;> norm_num

/-! ### The cascade of one source, netted -/

/-- The positive additions `Y_j → W_j` of a cascade: one at each state with
parameter at least 4. -/
def posFlow (Q : List ℕ) : ℕ → EdgeFlow
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | y + 4 => edgeUnit (cYW Q (y + 4)) + posFlow (Q ++ [2]) (y + 2)

/-- One unit on the edge of each charge of a list, with multiplicity. -/
def chargeFlow (l : List Charge) : EdgeFlow := (l.map fun ch => edgeUnit ch.label.edge).sum

lemma chargeFlow_nil : chargeFlow [] = 0 := rfl

lemma chargeFlow_cons (a : Charge) (l : List Charge) :
    chargeFlow (a :: l) = edgeUnit a.label.edge + chargeFlow l := by
  simp [chargeFlow]

/-- **Telescoping.**  For a state `(Q, y)` with `y ≥ 2`, the debt `-1` on
`X → Y` together with all cascade squares equals the positive additions
minus one unit on the edge of each charge of the forward construction: the
debts on the intermediate right peels cancel. -/
theorem cascade_net (Q : List ℕ) (y : ℕ) (hy : 2 ≤ y) :
    cascadeFlow Q y - edgeUnit (cXY Q y) = posFlow Q y - chargeFlow (cascade Q y) := by
  induction Q, y using cascade.induct with
  | case1 => omega
  | case2 => omega
  | case3 Q =>
    rw [cascadeFlow, posFlow, cascade, chargeFlow_cons, chargeFlow_nil, cXY_two]
    simp
  | case4 Q =>
    rw [cascadeFlow, posFlow, cascade, chargeFlow_cons, chargeFlow_nil, cXY_three]
    simp
  | case5 Q y ih =>
    have ih' := ih (by omega)
    have e : y + 4 - 2 = y + 2 := by omega
    rw [cascadeFlow, posFlow, cascade, chargeFlow_cons]
    unfold cascSquare squareFlow
    rw [cZW_eq_cXY_next Q (y + 4) (by omega), e, cXZ_eq]
    linear_combination ih'

/-- The corrections of one final-right source, netted. -/
theorem Source.net (s : Source) (ht : 2 ≤ s.t) :
    s.square + cascadeFlow s.P s.t
      = edgeUnit s.eAB + edgeUnit s.eBD - edgeUnit s.eAC + posFlow s.P s.t
        - chargeFlow s.trace := by
  have h := cascade_net s.P s.t ht
  unfold Source.square squareFlow Source.trace
  rw [Source.eCD_eq]
  linear_combination h

/-! ### The nine sums -/

/-- `Σ R [A → B]` over the left sources: cancels the nonfinal and final-left
`F_4` occurrences. -/
noncomputable def LAB (N : ℕ) : EdgeFlow := ∑ s ∈ leftSources N, s.rawDebit • edgeUnit s.eAB
/-- `Σ R [B → D]` over the left sources: a positive addition. -/
noncomputable def LBD (N : ℕ) : EdgeFlow := ∑ s ∈ leftSources N, s.rawDebit • edgeUnit s.eBD
/-- `Σ R [A → C]` over the left sources: the charges of row 1. -/
noncomputable def LAC (N : ℕ) : EdgeFlow := ∑ s ∈ leftSources N, s.rawDebit • edgeUnit s.eAC
/-- `Σ R [C → D]` over the left sources: the charges of row 2. -/
noncomputable def LCD (N : ℕ) : EdgeFlow := ∑ s ∈ leftSources N, s.rawDebit • edgeUnit s.eCD
/-- `Σ R [A → B]` over the final-right sources: cancels the final-right
`F_4` occurrences. -/
noncomputable def RAB (N : ℕ) : EdgeFlow := ∑ s ∈ rightSources N, s.rawDebit • edgeUnit s.eAB
/-- `Σ R [B → D]` over the final-right sources: a positive addition. -/
noncomputable def RBD (N : ℕ) : EdgeFlow := ∑ s ∈ rightSources N, s.rawDebit • edgeUnit s.eBD
/-- `Σ R [A → C]` over the final-right sources: the charges of row 3. -/
noncomputable def RAC (N : ℕ) : EdgeFlow := ∑ s ∈ rightSources N, s.rawDebit • edgeUnit s.eAC
/-- The positive additions `Y_j → W_j` of all cascades. -/
noncomputable def RPOS (N : ℕ) : EdgeFlow :=
  ∑ s ∈ rightSources N, s.rawDebit • posFlow s.P s.t
/-- The charges of rows 4–6: `R` on the edge of each charge of each
final-right source. -/
noncomputable def RCH (N : ℕ) : EdgeFlow :=
  ∑ s ∈ rightSources N, s.rawDebit • chargeFlow s.trace

/-- `f_d` as `f_0` plus the nine sums. -/
theorem fd_eq (N : ℕ) :
    fd N = f0 + LAB N + LBD N - LAC N - LCD N + RAB N + RBD N - RAC N + RPOS N - RCH N := by
  have hR : ∑ s ∈ rightSources N, s.rawDebit • (s.square + cascadeFlow s.P s.t)
      = ∑ s ∈ rightSources N, s.rawDebit •
          (edgeUnit s.eAB + edgeUnit s.eBD - edgeUnit s.eAC + posFlow s.P s.t
            - chargeFlow s.trace) :=
    sum_congr rfl fun s hs => by rw [s.net (mem_rightSources.1 hs).2.1]
  unfold fd LAB LBD LAC LCD RAB RBD RAC RPOS RCH
  rw [hR]
  simp only [LeftSource.square, squareFlow, smul_add, smul_sub, sum_add_distrib,
    sum_sub_distrib]
  abel

/-! ### Sums of indicators over a finite set of sources -/

/-- At most one source has a given key: the sum is bounded by any bound
valid for a matching source. -/
lemma sum_key_le {ι : Type*} (S : Finset ι) (key : ι → PEdge) (R : ι → ℚ) (e : PEdge) (B : ℚ)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, key s = key s' → s = s') (hB0 : 0 ≤ B)
    (hB : ∀ s ∈ S, key s = e → R s ≤ B) :
    ∑ s ∈ S, R s * (if key s = e then 1 else 0) ≤ B := by
  by_cases h : ∃ s₀ ∈ S, key s₀ = e
  · obtain ⟨s₀, hs₀, hk⟩ := h
    rw [sum_eq_single_of_mem s₀ hs₀ (fun s hs hne => by
        rw [if_neg (fun hk' => hne (hinj s hs s₀ hs₀ (hk'.trans hk.symm))), mul_zero]),
      if_pos hk, mul_one]
    exact hB s₀ hs₀ hk
  · rw [sum_eq_zero fun s hs => by rw [if_neg (fun hk => h ⟨s, hs, hk⟩), mul_zero]]
    exact hB0

lemma sum_key_nonneg {ι : Type*} (S : Finset ι) (key : ι → PEdge) (R : ι → ℚ) (e : PEdge)
    (hR : ∀ s ∈ S, 0 ≤ R s) : 0 ≤ ∑ s ∈ S, R s * (if key s = e then 1 else 0) :=
  sum_nonneg fun s hs => mul_nonneg (hR s hs) (by split_ifs <;> norm_num)

/-- A matching source contributes its own term. -/
lemma sum_key_ge {ι : Type*} (S : Finset ι) (key : ι → PEdge) (R : ι → ℚ) (e : PEdge)
    (hR : ∀ s ∈ S, 0 ≤ R s) (s₀ : ι) (hs₀ : s₀ ∈ S) (hk : key s₀ = e) :
    R s₀ ≤ ∑ s ∈ S, R s * (if key s = e then 1 else 0) := by
  have h := single_le_sum (f := fun s => R s * (if key s = e then 1 else 0))
    (fun s hs => mul_nonneg (hR s hs) (by split_ifs <;> norm_num)) hs₀
  simpa [hk] using h

/-! ### The nine sums, pointwise -/

lemma LAB_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LAB N c i p = ∑ s ∈ leftSources N, s.rawDebit * (if s.eAB = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [LAB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma LBD_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LBD N c i p = ∑ s ∈ leftSources N, s.rawDebit * (if s.eBD = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [LBD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma LAC_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LAC N c i p = ∑ s ∈ leftSources N, s.rawDebit * (if s.eAC = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [LAC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma LCD_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    LCD N c i p = ∑ s ∈ leftSources N, s.rawDebit * (if s.eCD = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [LCD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma RAB_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RAB N c i p = ∑ s ∈ rightSources N, s.rawDebit * (if s.eAB = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [RAB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma RBD_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RBD N c i p = ∑ s ∈ rightSources N, s.rawDebit * (if s.eBD = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [RBD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma RAC_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RAC N c i p = ∑ s ∈ rightSources N, s.rawDebit * (if s.eAC = ⟨c, i, p⟩ then 1 else 0) := by
  simp only [RAC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgeUnit_apply]

lemma RPOS_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RPOS N c i p = ∑ s ∈ rightSources N, s.rawDebit * posFlow s.P s.t c i p := by
  simp only [RPOS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma RCH_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    RCH N c i p = ∑ s ∈ rightSources N, s.rawDebit * chargeFlow s.trace c i p := by
  simp only [RCH, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `f_d` on an edge. -/
theorem fd_apply (N : ℕ) (c : List ℕ) (i p : ℕ) :
    fd N c i p = f0 c i p + LAB N c i p + LBD N c i p - LAC N c i p - LCD N c i p
      + RAB N c i p + RBD N c i p - RAC N c i p + RPOS N c i p - RCH N c i p := by
  rw [fd_eq]
  rfl

lemma posFlow_nonneg (Q : List ℕ) (y : ℕ) (c : List ℕ) (i p : ℕ) : 0 ≤ posFlow Q y c i p := by
  induction Q, y using posFlow.induct with
  | case1 => rw [posFlow]; exact le_refl _
  | case2 => rw [posFlow]; exact le_refl _
  | case3 => rw [posFlow]; exact le_refl _
  | case4 => rw [posFlow]; exact le_refl _
  | case5 Q y ih =>
    rw [posFlow]
    exact add_nonneg (edgeUnit_nonneg _ _ _ _) ih

/-! ### The flow of the charges, pointwise -/

lemma chargeFlow_apply (l : List Charge) (c : List ℕ) (i p : ℕ) :
    chargeFlow l c i p = (l.map fun ch => if ch.label.edge = ⟨c, i, p⟩ then (1 : ℚ) else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [chargeFlow_cons, List.map_cons, List.sum_cons, ← ih, ← edgeUnit_apply]
    rfl

/-- If, on a list, having the edge `(c, i, p)` is the same as being the
charge `ch₀`, the flow of the list on that edge is the multiplicity of
`ch₀`. -/
lemma chargeFlow_eq_count (l : List Charge) (ch₀ : Charge) (c : List ℕ) (i p : ℕ)
    (h : ∀ ch ∈ l, (ch.label.edge = ⟨c, i, p⟩ ↔ ch = ch₀)) :
    chargeFlow l c i p = (l.count ch₀ : ℚ) := by
  rw [chargeFlow_apply]
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun ch hch => h ch (List.mem_cons_of_mem a hch)
    rw [List.map_cons, List.sum_cons, hl]
    by_cases hc : a = ch₀
    · rw [if_pos (ha.2 hc), hc, List.count_cons_self]
      push_cast
      ring
    · rw [if_neg (fun h' => hc (ha.1 h')), List.count_cons_of_ne hc]
      ring

lemma chargeFlow_eq_zero (l : List Charge) (c : List ℕ) (i p : ℕ)
    (h : ∀ ch ∈ l, ch.label.edge ≠ ⟨c, i, p⟩) : chargeFlow l c i p = 0 := by
  rw [chargeFlow_apply]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, if_neg (h a List.mem_cons_self),
      ih fun ch hch => h ch (List.mem_cons_of_mem a hch), add_zero]

end K4
end ChowCone
