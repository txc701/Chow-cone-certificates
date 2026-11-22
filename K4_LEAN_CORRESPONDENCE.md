# Lean ⇄ manuscript correspondence, `k = 4`

Lean formalization of the combinatorial part of the fourth-moment certificate. Manuscript:
`CHOW_CONE_FLOWS_MANUSCRIPT.tex`, Sections 6–9, with the definitions of Section 5 that they
use. Lean files: `lean/ChowCone/K4/*.lean`, namespace `ChowCone.K4`. Toolchain and Mathlib are
those of the `k = 2` project (Lean `v4.32.2`, Mathlib `v4.32.2`); nothing in the `k = 2`
sources or the toolchain was changed. Sections 1–11 of the manuscript and the numbering of
every statement and equation are those of release `v1.0`; since then only the abstract,
Section 12 and the section on AI tools have changed, to describe this formalization. This
file complements `LEAN_CORRESPONDENCE.md`, which covers `k = 2`.

Releases: `v1.1` added the formalization; `v1.2` contains the changes made after the review
of `v1.1` described in the eighth section below. Dates in this file are UTC.

## Summary

The final statements are in `ChowCone.K4.UniformFlow` and `ChowCone.K4.Certificate`:

* `uniform_fourth_moment_flow` (Theorem 9.1): for every `d ≥ 1` there is an explicit flow on
  the compositions of `N = d + 2` that is nonnegative, has divergence `w^{(4)} = G S_4` at
  every composition, and is nonzero only on edges of the support DAG that split a block
  `n ↦ (p, n-p)` with `min(p, n-p) ≤ 3`.
* `fourth_moment_identity_on_support` and `fourth_moment_coefficient_sum_nonpos_on_support`
  (identity (39) and its sign): for every `d ≥ 1`, `Σ_J a_J^{(4)} N_J` equals the combination
  `Σ f(J,J') (N_J/U_J - N_{J'}/U_{J'})` over the edges carrying flow, and if `N_J / U_J` is
  monotone along those edges the sum is at most zero. Both sums run over the support
  compositions. The monotonicity is Cheng and Lin's Lemma 3.29; it is a hypothesis.
  `fourth_moment_identity`, `fourth_moment_certificate` and
  `fourth_moment_coefficient_sum_nonpos` are the same statements with the sums over all
  compositions of `d + 2`.

What stays outside Lean, as in the `k = 2` formalization: all matroid and Chow-ring theory,
Cheng and Lin's Lemma 3.29, the flag expansion (4), the derivation of `S_4` from the moments
of the flag summands in Section 5 (equations (16)–(17)), the values of `B_d` from Cheng and
Lin's Corollary 3.13 (equation (18)), and the step (19) from `Σ_J a_J^{(4)} N_J ≤ 0` to the
inequality of fourth moments. `S_4`, `B_d` and `a^{(4)}` are definitions taken from equations
(18), (20) and (21). Sections 10 and 11 are not treated.

The sections below follow the order in which the modules were written.

| module | content |
|---|---|
| `CascadeOrigins` | first milestone: origins and multiplicities of the charges of rows 4–6 |
| `CascadeSizes` | second: sizes `48 r_j` and the bounds of Lemma 8.1 |
| `SquareCharges` | third: origins of the charges of rows 1–3 |
| `SignedFlow` | fourth: `f_0`, Lemmas 6.1 and 6.2, Proposition 6.3 |
| `Rerouting` | fifth: the path squares, `f_d`, equation (34) |
| `Evaluation`, `Nonnegativity` | sixth: Proposition 8.2 |
| `UniformFlow`, `Certificate` | seventh: `d = 1, 2`, Theorem 9.1, identity (39) |

## First milestone: origins of the charges of rows 4–6 (`ChowCone.K4.CascadeOrigins`)

Fix a label of rows 4–6: the charged occurrence on the block `y + 2` of `Q.(y+2,2)`, with
`Q` a support composition (possibly empty), `y ≥ 2` and `sum Q + y + 4 = N`. Let `h` be the
length of the maximal trailing run of blocks equal to 2 in `Q`. A *source* is a tagged
final-right `F_4` occurrence on the last block of `P.(t+4)` with `t ≥ 2` and
`sum P + t + 4 = N`. The forward construction of Section 7 assigns to each source a list of
charges, one per stage. The theorem `cascade_charge_origins` says:

* for each `j = 0, …, h`, the source with `P = Q` minus its last `j` blocks and
  `t = y + 2j` charges the label at its stage `j`;
* these `h + 1` sources are pairwise distinct and are sources at the same `N`;
* no other stage of any source charges the label, so every source charges it as often as
  it occurs in that list (once or not at all), and the total multiplicity over all sources
  at `N` is `h + 1`.

Rows 4, 5 and 6 are the cases `y ≥ 4`, `y = 2` and `y = 3`.

## Second milestone: sizes of the charges (`ChowCone.K4.CascadeSizes`)

File `lean/ChowCone/K4/CascadeSizes.lean`. With `r_j = 2^j ρ₀(y+2j)/ρ₀(y)`,
`ρ₀(n) = (n-1)/n!` (equation (36); `ρ₀` is `blockTerm` of the `k = 2` files):

* the raw debit `48 G(P.(t,4))` of the `j`-th origin equals `48 r_j` times `G` of the child of
  the charged occurrence (`rawDebit_origin`);
* `r_{j+1}/r_j = 2/((y+2j+2)(y+2j-1))`, `Σ_{j ≤ h} r_j ≤ 25/16` for `y ≥ 2`, and
  `Σ_{j ≤ h} r_j ≤ 79/65` for `y = 3` (equations (37) and (38));
* summed over all sources at `N` with multiplicity, the label receives
  `48 Σ_{j ≤ h} r_j · G(child)`, which is at most `75 G(child)`, and strictly less than
  `60 G(child)` for a terminal `F_3` label.

The raw debit `R = 48 G(B)` is taken from the text of Section 7 as a definition
(`Source.rawDebit`). The flow `f_0` is defined in the fourth milestone, and the seventh
(`LAB_add_RAB`) shows that the corrections with this `R` cancel the `F_4` terms of `f_0`
exactly.

## Third milestone: origins of rows 1–3 (`ChowCone.K4.SquareCharges`)

File `lean/ChowCone/K4/SquareCharges.lean`. A *left source* is a tagged nonfinal or final-left
`F_4` occurrence on the block `t + 4` of `A = P.(t+4).S`; it is final-left exactly when `S` is
empty. Its square (28)–(29) charges the left `F_2` occurrence of the block `t + 4` of `A`
(row 1, edge `A → C`) and the left `F_2` occurrence of the block `t + 2` of `C = P.(2,t+2).S`
(row 2, edge `C → D`). The initial square (31) of a final-right source charges the right `F_2`
occurrence of the final block `t + 4` (row 3, edge `A → C = X_0`).

* In each row the charged occurrence determines the origin (`top_origin_unique`), and a source
  charges a label once or not at all (`LeftSource.count_row1`, `LeftSource.count_row2`,
  `Source.count_row3`).
* An origin exists exactly for: a selected left `F_2` occurrence of a block at least 6
  (row 1); a selected left `F_2` occurrence whose block is immediately preceded by a 2
  (row 2); a selected right `F_2` occurrence of a final block at least 6 (row 3).

The amounts (30) of these charges are computed in the sixth milestone.

## Fourth milestone: the signed flow `f_0` (`ChowCone.K4.SignedFlow`)

File `lean/ChowCone/K4/SignedFlow.lean`. Flows are functions of positional edges
`(c, i, p)`, as `F` in the `k = 2` files, and `divOf f c = outSumOf f c - inSumOf f c` is
defined exactly as `flowDiv` there (`divOf_F` is `rfl`).

* The primitive flows `F_s` (`prim s`) give every selected occurrence of `F_s` the raw flow
  `G(child)`; `F_2` is the `k = 2` flow (`prim_two`). The indicators are those of the tagged
  occurrences of the first milestone (`indNs_eq_one_iff` and its two companions).
* **Lemma 6.1** (`primitive_divergences`): at every support composition of `N ≥ 5`,
  `div F_s = G · T_s` for `s = 2, 3, 4`.
* **Lemma 6.2** (`divOf_F2V`): `div F_{2,V} = G · (V(V-N)/2 - 6 T_3 - 2V)`.
* **Proposition 6.3** (`divOf_f0`): for
  `f_0 = 30 F_{2,V} + (30N-12) F_2 + 72 F_3 - 48 F_4` and `d ≥ 3`, `div f_0 = w^{(4)}` at
  every support composition of `N = d + 2`, where `w^{(4)} = G · S_4` and
  `S_4 = 15V^2 - 6Q_2 - 12V - (15N^2 - 6N)`.

The three statements are derived from one general theorem, `divOf_wprim`, on the divergence
of a flow that gives every selected occurrence of `F_s` the raw flow `φ(child) G(child)`, for
any `s ≥ 1` and any weight `φ` that agrees on the two children of a final block.

Limits of this milestone. `S_4` and `B_d = 15N^2 - 6N` are taken from equations (18) and (21)
as definitions; the derivation of `S_4` from the moments of the flag summands in Section 5 and
the value of `B_d` from Cheng and Lin's Corollary 3.13 are not formalized. The divergence is
the positional one; its identification with the divergence on the vertices of the Boolean
lattice is proved for every positional flow in the seventh milestone.

## Fifth milestone: the rerouting and the flow `f_d` (`ChowCone.K4.Rerouting`)

File `lean/ChowCone/K4/Rerouting.lean`.

* `edgeUnit e` is the unit flow on a positional edge `e`; its divergence is `+1` at the parent
  and `-1` at the child (`divOf_edgeUnit`). A path square `squareFlow` is the difference of the
  edge chains of two paths with the same ends, and has zero divergence (`divOf_squareFlow`).
* The left square (29) of a nonfinal or final-left source, the final-right square (31) and the
  cascade squares (33) are defined on the edges named in the manuscript, and each has zero
  divergence. The edges are identified with the occurrences of the earlier milestones: `A → B`
  is the `F_4` occurrence, `A → C` and `C → D` are the labels of rows 1, 2 and 3, `X → Z` is
  the label of row 4, and `Z_j → W_j` is `X_{j+1} → Y_{j+1}`.
* `fd N` is `f_0` plus `R` times the left square of every left source at size `N`, plus `R`
  times the final-right square and all cascade squares of every final-right source at size `N`,
  with `R = 48 G(B)`.
* **Equation (34)** (`divOf_fd`): for `d ≥ 3`, `div f_d = w^{(4)}` at every support composition
  of `N = d + 2`.
* The vertices of all squares of valid sources are support compositions (`square_supp`,
  `cascSquare_supp`).

Not in this milestone: the values of `f_d` on edges and their nonnegativity.

## Sixth milestone: nonnegativity of `f_d` (`ChowCone.K4.Evaluation`, `ChowCone.K4.Nonnegativity`)

Files `lean/ChowCone/K4/Evaluation.lean` and `lean/ChowCone/K4/Nonnegativity.lean`.

* **Telescoping** (`cascade_net`): for one final-right source, the debt on `X → Y` together
  with all cascade squares equals the positive additions `Y_j → W_j` minus one unit on the
  edge of each charge of the forward construction of the first milestone. The debts on the
  intermediate right peels cancel, whatever else those edges carry.
* **Evaluation** (`fd_eq`, `fd_apply`): `f_d` is `f_0` plus nine sums over the sources, one for
  each role of an edge in a square: `A → B`, `B → D`, `A → C`, `C → D` of the left squares,
  `A → B`, `B → D`, `A → C` of the final-right squares, the additions `Y_j → W_j`, and the
  charges of rows 4–6.
* **Amounts of rows 1–3** (`amount_AC_nonfinal`, `amount_AC_final`, `amount_CD`,
  `amount_right_AC`): `48 G(B)` equals `12(t+2)(t-1) G(C)` or `12t(t-1) G(C)`, `24 G(D)`,
  and `24(t+2)(t-1) G(C)`, as in equation (30) and the text after (31).
* **Bounds on the nine sums.** The two `A → B` sums put at least `48 G(child)` on the edge of
  every `F_4` occurrence (`LAB_ge`, `RAB_ge`). The three additions are nonnegative. The sums
  of rows 1, 2 and 3 are bounded by the amounts above times `G(child)` on an edge that
  carries the corresponding `F_2` occurrence, and by zero on any other edge (`LAC_le`,
  `LCD_le`, `RAC_le`); this uses that a label has at most one origin. The sum of rows 4–6 is
  at most `75 G(child)` on an edge with a nonfinal `F_2` occurrence, at most `60 G(child)` on
  an edge with a nonfinal `F_3` occurrence, and at most zero elsewhere (`RCH_le`); this uses
  the list of origins of the first milestone and the bounds of the second. The four sums are
  also nonnegative (`LAC_nonneg`, `LCD_nonneg`, `RAC_nonneg`, `RCH_nonneg` in
  `UniformFlow`), so they vanish where the bound is zero.
* **Margins** (`margin_N2`, `margin_FL2`, `margin_FR2`): the reserve (35) minus the largest
  possible charges is nonnegative. The statements contain no polynomial; with the reserve
  bounded below by `V(child) ≥ (M-2)(M-4)` and `N ≥ M + 2` or `N ≥ M`, the proofs reduce
  to the three margin polynomials `18M^2 - 66M + 69`, `18M^2 - 42M - 36`, `6M^2 + 18M - 12`
  for `M ≥ 6` and to the cases `M = 4, 5`. The manuscript states strict inequalities; the
  Lean states `≥ 0`.
* **Proposition 8.2** (`fd_nonneg`): for every `N`, every edge value of `f_d` on the
  compositions of `N` is nonnegative. The hypothesis `d ≥ 3` of the manuscript is not needed
  for this statement.

Two points where the Lean proof is organized differently from the text. First, the estimates
are made on edges, with the occurrences on an edge counted by the indicators `indNs`,
`indFLs`, `indFRs`; the reserves of coincident occurrences add because the indicators add.
Second, for the cancellation of the `F_4` occurrences this milestone uses only the inequality
"at least `48 G(child)`", which is what nonnegativity needs; the exact cancellation is proved
in the seventh milestone.

## Seventh milestone: Theorem 9.1 and the certificate (`ChowCone.K4.UniformFlow`, `ChowCone.K4.Certificate`)

Files `lean/ChowCone/K4/UniformFlow.lean` and `lean/ChowCone/K4/Certificate.lean`.

* **Exact cancellation** (`LAB_add_RAB`, `fd_apply_cancelled`): the corrections put exactly
  `48 G(child)` on the edge of every `F_4` occurrence, so on every edge `f_d` is the reserves
  of the `F_2` and `F_3` occurrences, plus the additions, minus the charges of rows 1–6.
* **Support of the flow** (`fd_eq_zero_of_wide`): if both parts of a split are at least 4,
  the edge carries no flow.
* **Off the support** (`divOf_f0_all`): Proposition 6.3 holds at every composition of `N ≥ 5`
  with positive parts; where some part is 1 both sides vanish.
* **Boundary dimensions** (`Bd`, `w4d_one`, `divOf_fdAll_two`): `B_1 = 45` and `S_4(3) = 0`;
  `B_2 = 240`, `G(4) = G(2,2) = 3`, and the raw flow `720` on `(4) → (2,2)`.
* **Theorem 9.1** (`uniform_fourth_moment_flow`): for every `d ≥ 1`, with
  `fdAll d` equal to `0`, to `720 [(4) → (2,2)]`, or to `f_d`.
* **Vertex form** (`fEdgeOf`, `sum_fEdgeOf_out`, `sum_fEdgeOf_in`, `fEdgeOf_div`): for any
  positional flow, the divergence on the vertices `Composition n` equals the positional
  divergence. This generalizes `sum_fEdge_out` and `sum_fEdge_in` of the `k = 2` file
  `ChowCone.Main`, which treat the flow `F`.
* **Certificate** (`fourth_moment_identity`, `fourth_moment_certificate`,
  `fourth_moment_coefficient_sum_nonpos`): the finite-poset flow lemma of the `k = 2` file
  `ChowCone.Abstract` applied to `fEdge4`.

As in the `k = 2` formalization, the vertex type is Mathlib's `Composition (d+2)`. It has
`2^(d+1)` elements, where the Boolean lattice of the manuscript has `2^d`: it also contains
the compositions whose final part is 1, which are not flag types. On them `G`, hence
`w^{(4)}` and `a^{(4)}`, vanishes, and no edge carrying flow meets them. In `v1.1` the last
fact was stated here in prose only. Since `v1.2` it is a theorem; see the next section.

## Eighth section: the review of `v1.1` and the changes of `v1.2`

Release `v1.1` was reviewed on 22 November 2026 by five sessions of the AI system that wrote
the formalization, each started afresh with one criterion (substantiveness, correspondence,
faithfulness to Sections 5–7, faithfulness to Sections 8–9, non-vacuity), the repository at
`v1.1` and the manuscript, and nothing from the authoring session. `RELEASE_CHECKS.md` has
the record. Of 180 items, 163 passed, 9 failed and 8 were marked ambiguous; no item concerns a
false statement. The changes of `v1.2` answer them.

* **The flow lives on the support DAG** (`SuppEdge`, `fd_eq_zero_of_not`,
  `fdAll_ne_zero_suppEdge`, `fdAll_ne_zero_supp`, `fEdge4_ne_zero_supp`): an edge that carries
  flow has a support parent and splits a block into two parts at least 2, so both of its ends
  are support compositions. The third clause of `uniform_fourth_moment_flow` and the
  conclusion of `fEdge4_ne_zero_cover` now say this. Four of the five reviews had asked for
  it: it is what makes the hypothesis `hmono` an instance of Cheng and Lin's Lemma 3.29.
* **The offsets of Section 2** (`outSumOf_fdAll_suppEdges`, `divOf_fdAll_suppEdges`): the Lean
  divergence sums over every offset `1 ≤ p ≤ n_i - 1`, also for the final block, where
  Section 2 allows only `p ≤ n_r - 2`. The flow vanishes on the additional edges, and the
  divergence identity of Theorem 9.1 holds with the offsets `2 ≤ p ≤ n_i - 2` alone.
* **Identity (39) on the lattice of the manuscript** (`suppComps`, `a4d_eq_zero_of_not_supp`,
  `lastPart_ge_two_of_supp`, `fourth_moment_identity_on_support`,
  `fourth_moment_coefficient_sum_nonpos_on_support`): both sums restricted to the support
  compositions, and monotonicity assumed only between support compositions joined by an edge
  carrying flow. `fourth_moment_identity` states (39) without the monotonicity hypothesis.
* **Hypotheses and duplicates.** `fourth_moment_certificate` no longer has the hypothesis
  `U ≠ 0`, which its proof did not use. `cascade_charge_origins` is stated for a size `N`
  without the unused `3 ≤ d`. `uniform_nonnegativity` (an instance of `fd_nonneg` with an
  unused `3 ≤ d`) and `signed_flow_divergence` (a restatement of `divOf_f0`) were removed.
  The symmetry hypothesis of `divOf_wprim` is asked only for final blocks `m ≥ s + 2`.
* **Wording.** The docstrings of `LAC_le`, `LCD_le`, `RAC_le`, `RCH_le` and of the three
  margin lemmas, the table below (qualified names) and the passages of this file that the
  review found inexact.

The lemmas of the first three items were first proved in probes of the reviewers and were
adapted from there.

## What is not proved

Everything listed under "What stays outside Lean" in the summary. Inside the combinatorial
part, two items are not formalized: closed formulas for the additions `B → D` and
`Y_j → W_j` on an edge (they are only shown to be nonnegative, and zero on edges whose two
parts are at least 4), and the diagnostic value check of `f_d` for `N = 6`, which was done by
hand.

## Design decisions affecting fidelity

* **Compositions as `List ℕ`**, with `Supp` and `splitAt` from the `k = 2` files. An edge is
  a pair (parent, `splitAt parent i p`).
* **Tagged occurrences.** `Occ` records the primitive index `s`, a tag (`nonfinal`,
  `finalLeft`, `finalRight`), the parent and the block index. Occurrences with different tags
  are different terms even when their edges coincide (final block 8 for `s = 4`).
  `Occ.Selected` restates the selection rule of Section 6.
* **Sources** are pairs `(P, t)`. `selected_finalRight_F4_iff` proves that the sources at
  size `N` are exactly the selected final-right `F_4` occurrences on compositions of `N`.
* **The forward construction** is the function `cascade`, defined by recursion on `y` with
  the three cases of the manuscript. It does not mention trailing runs or origins. Its value
  is a list, so charges are counted with multiplicity.
* **`d ≥ 3`.** `cascade_charge_origins` and its supporting theorems are stated for an
  arbitrary size `N`; the hypotheses force `N ≥ 6`, that is `d ≥ 4`.
* **Junk values.** `cascade Q 0 = cascade Q 1 = []`. These parameters do not occur for a
  source, since `t ≥ 2` and each stage lowers the parameter by 2 only when it is at least 4.
  `chargeAt Q y` for `y < 2` is the row-4 form and is never used; every theorem that needs
  it assumes `2 ≤ y`.
* **Positional flows.** A flow is a function of `(c, i, p)`: split block `i` of `c` at offset
  `p`. Divergence is `outSumOf - inSumOf`, written as `flowDiv` in the `k = 2` files. The
  passage to vertex pairs is `fEdgeOf`.
* **`fd N` and `fdAll d` are indexed by the size.** Their statements assume `c.sum = N`. On a
  composition of another size `fd N` is `f_0`, which has negative values; this is outside the
  domain of the theorems.
* **Where `d ≥ 3` is needed.** Nonnegativity of `fd N` holds for every `N`. The divergence
  identities need `N ≥ 5` (`divOf_f0`) or `3 ≤ d` (`divOf_fd`); for `d = 1, 2` the flow and the
  constant `B_d` are those of Section 9 (`fdAll`, `Bd`).
* **Definitions taken from the manuscript, not derived.** `S4`, `S4d`, `Bd`, `a4`, `a4d`
  (equations (18), (20), (21)) and the raw debit `48 G(B)`.
* **Vertices and offsets.** `Composition (d+2)` contains compositions with final part 1,
  which are not flag types, and the Lean divergence admits the final offset `p = n_r - 1`,
  which Section 2 excludes. The flow vanishes on every edge that is not an edge of the
  support DAG; see the eighth section.

## Table

| Lean name | Manuscript | Statement |
|---|---|---|
| `Tag`, `Occ`, `Occ.child`, `Occ.Selected` | Section 6, move multisets `F_s` | tagged selected occurrences and their edges |
| `Source`, `Source.Valid`, `Source.occ` | Section 7, final-right `F_4` occurrence, (31) | the occurrence `P.(t+4) → P.(t,4)` |
| `selected_finalRight_F4_iff` | Section 6 and (31) | sources at `N` = selected final-right `F_4` occurrences on compositions of `N` |
| `Source.leftOcc`, `Source.leftOcc_ne_occ`, `Source.leftOcc_child_eq_iff` | Section 7, "the two occurrences of `8 ↦ (4,4)` are canceled separately" | the final-left label is a different occurrence; same edge iff `t = 4` |
| `sqX`, `sqY`, `sqZ`, `sqW` | (32) at a state `(Q, y)` | `Q.(y+2,2)`, `Q.(y,2,2)`, `Q.2.(y,2)`, `Q.2.(y-2,2,2)` |
| `X`, `Y`, `Z`, `W` | (32), `X_j, Y_j, Z_j, W_j` | the same with `Q = P.2^j`, `y = t - 2j` |
| `sqY_eq_splitAt`, `sqZ_eq_splitAt`, `sqW_eq_splitAt_sqY`, `sqW_eq_splitAt_sqZ` | the four edges of the square (33) | each is a `splitAt` of the stated block at the stated offset |
| `sqZ_eq_sqX_next`, `sqW_eq_sqY_next`, `Z_eq_X_succ`, `W_eq_Y_succ` | "moves the same debt to `Z_j → W_j`" | `Z_j = X_{j+1}` (when stage `j` exists), `W_j = Y_{j+1}` |
| `sqX_eq_splitAt_source`, `sqY_eq_splitAt_source_child` | (31), `C` and `D` | `C = X_0` is the right peel of `A`; `D = Y_0` is the split `4 ↦ (2,2)` of `B` |
| `sqZ_ne_sqY` | Section 8, paragraph before Table 1 | for `y ≥ 4` the consumed edge `X → Z` is not the debit edge `X → Y` |
| `Row`, `Charge`, `leftF2`, `nonfinalF3` | Table 1, rows 4–6, column "charged occurrence" | the `F_2` occurrence `(y+2) ↦ (2,y)` and the `F_3` occurrence `5 ↦ (3,2)` before the final block 2 |
| `cascade`, `Source.trace` | Section 7, the recursive transfer after (31) | the forward construction |
| `chargeAt` | Table 1, rows 4–6 | the row and label at `Q.(y+2,2)` |
| `chargeAt_selected`, `indN_leftF2` | Table 1, "selected occurrence" | the label is selected; for the `F_2` labels the `k = 2` indicator `indN` equals 1 |
| `chargeAt_row`, `chargeAt_child`, `stage_edge` | Table 1, column "negative term" | row by `y`; edge `X_j → Z_j` for `y ≥ 4`, the debit edge `X_j → Y_j` for `y = 2, 3` |
| `cascade_getElem?`, `cascade_stage_iff`, `cascade_length` | Section 7, "each step lowers `y` by two" | stage `j` exists iff `2j + 2 ≤ t`; then prefix `P.2^j` and `t = y + 2j` |
| `cascade_nodup` | — | a source charges a label at most once |
| `trailingTwos`, `eq_append_replicate_iff`, `exists_eq_append_replicate_iff`, `append_replicate_unique` | Lemma 8.1, "suffixes of the run of consecutive 2-blocks" | `Q = P.2^j` is solvable iff `j ≤ h`; `P` is unique |
| `origin`, `origins`, `origin_valid`, `origin_injective`, `origins_nodup`, `origins_length` | Lemma 8.1, "an origin is recovered uniquely by deleting a suffix … and replacing `y` by `y + 2j`" | the `h + 1` origins, valid and distinct |
| `trace_stage_eq_chargeAt_iff`, `origin_trace`, `origin_of_stage` | Lemma 8.1; Table 1, column "how many" | stage `j` of `s` charges the label iff `j ≤ h` and `s` is the `j`-th origin |
| `chargeAt_mem_trace_iff`, `count_trace_eq_count_origins` | the same, with multiplicity | count in the trace of `s` = count of `s` among the origins |
| `validSources_finite`, `sum_count_trace`, `total_multiplicity` | "one for each `j = 0, …, h`" | total multiplicity over all sources at `N` is `h + 1` |
| `mem_trace_iff`, `label_s_of_mem_trace`, `leftF2_three_not_charged` | Section 8, the paragraph on the blocks 4 and 5 before a final 2 | only these labels are charged; never an `F_4` label; never the `F_2` label `5 ↦ (2,3)` |
| `cascade_charge_origins` | Lemma 8.1 (origins only) and Table 1, rows 4–6 | the assembled statement |
| `r`, `r_zero`, `r_pos` | (36) | `r_j = 2^j ρ₀(y+2j)/ρ₀(y)` |
| `blockTerm_add_two`, `r_succ` | proof of Lemma 8.1; (37), first formula | `ρ₀(n+2)/ρ₀(n) = 1/((n+2)(n-1))`; the ratio `r_{j+1}/r_j` |
| `sum_r_le` | (37), second formula | `Σ_{j ≤ h} r_j ≤ 25/16` |
| `sum_r_three_le` | (38) | `Σ_{j ≤ h} r_j ≤ 79/65` at `y = 3` |
| `Source.rawDebit` | Section 7, `R = 48 G(B)` | definition, taken from the text |
| `G_source_child_eq`, `G_sqY_eq_sqZ`, `rawDebit_origin` | Lemma 8.1, "cancellation of all unaffected factors in `G` gives (36)"; Table 1, rows 4–6, "normalized amount" | the `j`-th origin charges `48 r_j · G(child)` |
| `total_charge`, `total_charge_le`, `total_charge_F3_lt` | the sentence after Lemma 8.1 | all cascades together: at most 75 units, fewer than 60 on a terminal `F_3` label |

| `LeftSource`, `LeftSource.Valid`, `LeftSource.occ`, `leftTag` | Section 7, (28): nonfinal or final-left `F_4` occurrence | the occurrence `P.(t+4).S → P.(4,t).S` |
| `selected_left_F4_iff` | Section 6 and (28) | left sources at `N` = selected nonfinal and final-left `F_4` occurrences on compositions of `N` |
| `LeftSource.row1Label`, `LeftSource.row1Label_parent`, `LeftSource.row1Label_child` | Table 1, row 1 | left `F_2` occurrence of the block `t+4` of `A`; edge `A → C` |
| `LeftSource.row2Label`, `LeftSource.row2Label_parent`, `LeftSource.row2Label_child` | Table 1, row 2 | left `F_2` occurrence of the block `t+2` of `C`; edge `C → D` |
| `LeftSource.occ_child`, `LeftSource.square_closes` | (28) | `B = P.(4,t).S`; `B → D` is the split `4 ↦ (2,2)` |
| `Source.row3Label`, `Source.row3Label_parent`, `Source.row3Label_child` | Table 1, row 3; (31) | right `F_2` occurrence of the final block `t+4`; edge `A → C = X_0` |
| `LeftSource.row1Label_selected`, `LeftSource.row2Label_selected`, `Source.row3Label_selected` | Table 1, "charged occurrence" | the labels are selected `F_2` occurrences |
| `TopRow`, `TopCharge`, `LeftSource.charges`, `Source.topCharges`, `LeftSource.count_row1`, `LeftSource.count_row2`, `Source.count_row3` | Table 1, rows 1–3, "at most one" | each source charges a label once or not at all |
| `LeftSource.row1Label_injective`, `LeftSource.row2Label_injective`, `Source.row3Label_injective`, `top_origin_unique` | "For types 1–3, the charged occurrence and the type determine the origin" | at most one origin |
| `row1_origin_exists_iff`, `row3_origin_exists_iff` | Table 1, rows 1 and 3, "the block is at least 6" | when an origin exists |
| `row2_origin_exists_iff` | Table 1, row 2, "needs the preceding 2"; "recovered by merging the affected block with the 2 immediately preceding it" | when an origin exists |

| `EdgeFlow`, `outSumOf`, `inSumOf`, `divOf`, `divOf_F` | Lemma 3.1, definition of `div` | positional divergence; equal to `flowDiv` for the `k = 2` flow |
| `indNs`, `indFLs`, `indFRs`, `ind`, `indNs_eq_one_iff`, `indFLs_eq_one_iff`, `indFRs_eq_one_iff` | Section 6, the move multiset `F_s` | indicators of the selected occurrences; `ind` is 2 on a balanced final edge |
| `wprim`, `prim`, `prim_two` | Section 6, "give every selected move raw flow `G(child)`" | `F_s`; `F_2 = F` |
| `tau`, `G_ratio_N'`, `G_ratio_FL'`, `G_ratio_FR'`, `G_splitAt_nonfinal'`, `G_splitAt_final_left'`, `G_splitAt_final_right'` | proof of Lemma 6.1, first paragraph | `G(child)/G(parent)`; the final ratios `(m-s)/m` and `s/m` |
| `tau3`, `tau4`, `tau_two`, `tau_three`, `tau_four` | (22) | `τ_2 = ρ`, `τ_3(n) = n(n-2)(n-4)/3`, `τ_4(n) = n(n-2)(n-3)(n-5)/8` |
| `block_two`, `block_three`, `block_four` | proof of Lemma 6.1, "`τ_s(s) = -1`, and `τ_s` vanishes at every other support size below `s+2`" | per-block balance |
| `ind_merge`, `wprim_merge`, `inSumOf_wprim` | proof of Lemma 6.1, second paragraph | every block equal to `s` has one incoming selected occurrence; `(s)` alone is excluded |
| `outSumOf_wprim`, `divOf_wprim` | proof of Lemma 6.1 | divergence of a weighted primitive flow |
| `T2`, `T3`, `T4`, `divOf_prim_two`, `divOf_prim_three`, `divOf_prim_four`, `primitive_divergences` | Lemma 6.1, (23) | `div F_s = G T_s` |
| `vq`, `V`, `Q2`, `F2V`, `V_splitAt`, `T2_eq`, `divOf_F2V` | Lemma 6.2, (24) | the discrete product rule |
| `Q2_sub_nine_V` | (25), (26) | `Q_2 - 9V = 8T_4 + 18T_3` |
| `f0`, `f0_eq`, `divOf_f0_eq` | (27) and the sentence "Equivalently, …" | the signed flow, occurrence by occurrence; linearity |
| `S4`, `w4`, `a4`, `w4_eq_U_mul_a4`, `Bd_eq` | (18), (20), (21) | `w^{(4)} = G S_4 = U a^{(4)}`; `B_d = 3(d+2)(5d+8)` |
| `divOf_f0` | Proposition 6.3 | `div f_0 = w^{(4)}` for `d ≥ 3` |

| `divOf_add`, `divOf_smul`, `divOf_sub`, `divOf_sum` | Section 7, "every correction has zero divergence, and therefore …" | linearity of the divergence |
| `PEdge`, `PEdge.child`, `PEdge.Valid`, `Occ.edge`, `edgeUnit`, `divOf_edgeUnit` | Section 7, the unit flow `[A → B]` | divergence `+1` at `A`, `-1` at `B` |
| `squareFlow`, `divOf_squareFlow` | Section 7, "the difference of the edge chains of two directed paths with the same initial and terminal vertices has zero divergence" | path squares |
| `LeftSource.eAB`, `LeftSource.eBD`, `LeftSource.eAC`, `LeftSource.eCD`, `LeftSource.square`, `LeftSource.rawDebit`, `LeftSource.divOf_square` | (28), (29) | the left square and `R = 48 G(B)` |
| `LeftSource.eAB_eq`, `LeftSource.eAC_eq`, `LeftSource.eCD_eq` | (29), Table 1 rows 1–2 | the edges are the `F_4` occurrence and the labels of rows 1 and 2 |
| `Source.eAB`, `Source.eBD`, `Source.eAC`, `Source.eCD`, `Source.square`, `Source.divOf_square`, `Source.eAB_eq`, `Source.eAC_eq`, `Source.eCD_eq` | (31), Table 1 row 3 | the final-right square; `C → D` is the first debt edge |
| `cXY`, `cYW`, `cXZ`, `cZW`, `cascSquare`, `cascadeFlow`, `divOf_cascSquare`, `divOf_cascadeFlow` | (32), (33) | the cascade squares of one source |
| `cXZ_eq`, `cXY_two`, `cXY_three`, `cZW_eq_cXY_next` | Section 7, the recursive transfer; Table 1 rows 4–6 | the cascade edges are the labels of rows 4–6; the debt moves to the next debt edge |
| `validLeftSources_finite`, `leftSources`, `rightSources` | "apply … to every labeled … occurrence" | the finite sets of sources at size `N` |
| `fd`, `divOf_fd_eq_divOf_f0`, `divOf_fd` | definition of `f_d`; (34) | `div f_d = w^{(4)}` for `d ≥ 3` |
| `LeftSource.square_supp`, `Source.square_supp`, `cascSquare_supp` | "all vertices … in the path squares are support vertices" | support of the square vertices |

| `posFlow`, `chargeFlow`, `cascade_net`, `Source.net` | Section 8, "the two terms cancel, regardless of any other label on the edge" | telescoping of the debts of one source |
| `LAB`, `LBD`, `LAC`, `LCD`, `RAB`, `RBD`, `RAC`, `RPOS`, `RCH`, `fd_eq`, `fd_apply` | Section 7, definition of `f_d`; Table 1, column "negative term" | `f_d` as `f_0` plus nine sums |
| `sum_key_le`, `sum_key_ge`, `chargeFlow_eq_count` | Table 1, column "how many" | at most one source per key; multiplicity of a charge |
| `amount_AC_nonfinal`, `amount_AC_final`, `amount_CD`, `amount_right_AC` | (30); text after (31); Table 1 rows 1–3, "normalized amount" | `12(t+2)(t-1)`, `12t(t-1)`, `24`, `24(t+2)(t-1)` |
| `LAB_ge`, `RAB_ge` | "this cancels the negative `F_4` occurrence on `A → B`" | at least `48 G(child)` per `F_4` occurrence |
| `LBD_nonneg`, `RBD_nonneg`, `RPOS_nonneg` | "every correction not listed above adds rather than subtracts flow" | the additions are nonnegative |
| `a1n`, `a1f`, `a3`, `LAC_le`, `LCD_le`, `RAC_le` | Table 1 rows 1–3 | total charge of each row on an edge |
| `chargeAt_edge`, `chargeAt_edge_injective`, `RCH_le_of_charge`, `RCH_le` | Table 1 rows 4–6; the sentence after Lemma 8.1 | at most `75` units on a nonfinal `F_2` edge, `60` on a nonfinal `F_3` edge |
| `vq_le_V`, `two_blocks_le_sum`, `margin_N2`, `margin_FL2`, `margin_FR2` | proof of Proposition 8.2 | the three margin polynomials and `M = 4, 5` |
| `fd_nonneg` | Proposition 8.2 | every edge value of `f_d` is nonnegative |
| `LAB_le`, `RAB_le`, `LAB_add_RAB`, `fd_apply_cancelled` | Section 7, "this cancels the negative `F_4` occurrence on `A → B`" | exact cancellation |
| `fd_eq_zero_of_wide`, `fdAll_used_edge` | Section 7, "all surviving flow is supported on peel-two and peel-three cover edges"; Theorem 9.1, last sentence | `min(p, n-p) ≤ 3` on every edge carrying flow |
| `divOf_f0_of_not_supp`, `divOf_f0_all` | Section 9, "off the support `w^{(4)} = 0`, and no selected edge is incident" | divergence at every composition |
| `Bd`, `S4d`, `w4d`, `a4d`, `w4d_eq_U_mul_a4d`, `w4d_eq_w4` | (18), (20), (21) | the target for every `d` |
| `fdAll`, `w4d_one`, `divOf_fdAll_two`, `G_four`, `G_two_two` | Section 9, `d = 1` and `d = 2` | `f_1 = 0`; raw flow `720` on `(4) → (2,2)` |
| `divOf_fdAll`, `fdAll_nonneg`, `uniform_fourth_moment_flow` | Theorem 9.1 | the uniform fourth-moment flow |
| `fEdgeOf`, `fEdgeOf_F`, `sum_fEdgeOf_out`, `sum_fEdgeOf_in`, `fEdgeOf_div` | Section 2, Boolean covers as splits; Lemma 3.1 | vertex divergence = positional divergence |
| `fEdge4`, `fEdge4_nonneg`, `fEdge4_div`, `fEdge4_ne_zero_cover` | Section 9, "extend `f_d` by zero to the full Boolean lattice" | the flow on `Composition (d+2)`; a pair with flow is a split into two parts at least 2 with `min(p, n-p) ≤ 3` |
| `fourth_moment_identity`, `fourth_moment_certificate` | (39) and the sentence after it | identity, and its sign with Lemma 3.29 as hypothesis, for arbitrary `N`, `U` on all compositions |
| `U_ne_zero`, `U_comp_ne_zero`, `fourth_moment_coefficient_sum_nonpos` | (3), (20), (39) | `Σ a^{(4)} N ≤ 0` with the Boolean flag numbers, the sum over all compositions |
| `SuppEdge`, `fd_eq_zero_of_not`, `fdAll_ne_zero_suppEdge`, `fdAll_ne_zero_supp`, `fEdge4_ne_zero_supp` | Theorem 9.1, "a nonnegative flow on the support-composition DAG" | an edge carrying flow joins two support compositions |
| `LAC_eq_zero_of_not`, `LCD_eq_zero_of_not`, `RAC_eq_zero_of_not`, `RCH_eq_zero_of_not`, `LBD_eq_zero_of_not`, `RBD_eq_zero_of_not`, `RPOS_eq_zero_of_not` | Table 1; Section 7 | each of the sums vanishes off the support DAG |
| `outSumOf_fdAll_suppEdges`, `divOf_fdAll_suppEdges` | Section 2, the allowed offsets; Theorem 9.1 | the divergence with the offsets `2 ≤ p ≤ n_i - 2` only |
| `suppComps`, `lastPart_ge_two_of_supp`, `a4d_eq_zero_of_not_supp`, `fourth_moment_identity_on_support`, `fourth_moment_coefficient_sum_nonpos_on_support` | (39) and its sign, the sums over `J ⊆ [d]` | the certificate with both sums over the support compositions |

## Diagnostic examples (in the file, section `Examples`)

* `Q = (2,2)`, `y = 2`: `h = 2`; the origins are the final-right labels of `(2,2,6)`, `(2,8)`
  and `(10)`; no source charges the label at stage 3.
* `Q = ()`, `y = 3`: the charge is on the `F_3` label `(5,2) → (3,2,2)`; the left `F_2` label
  `(5,2) → (2,3,2)` is never charged.
* `Q = ()`, `y = 4`: `(8) → (4,4)` has a final-left and a final-right label and only the
  second is a source. Its trace has two charges. The intermediate debit edge
  `(6,2) → (4,2,2)` is also the edge of a selected nonfinal `F_4` occurrence, and the trace
  contains no charge on that occurrence.
* `Q = (2,3)`, `y = 2`: `h = 0`, one origin.

Examples of `SquareCharges`: the square of the nonfinal block 6 of `(6,2)`, whose row-2 label
`(2,4,2) → (2,2,2,2)` is also the row-5 label of the cascade at `Q = (2)`, `y = 2`; the final
block 8, whose two `F_4` labels charge different `F_2` occurrences; a block 5, which has no
row-1 origin; the block 5 of `(2,5,2)`, whose row-2 origin is on `(7,2)`.

Values in `SignedFlow`, computed from the definitions and not from the theorem: for `N = 5`,
`f_0` is `3600` on `(5) → (2,3)` and `2400` on `(5) → (3,2)`, and `w^{(4)}(5) = 6000`; the
balanced edge `(8) → (4,4)` carries two `F_4` occurrences.

## Verification (2026-11-21 and 2026-11-22)

`RELEASE_CHECKS.md` has the full record for each release. For `v1.2`, in a fresh worktree
with the `.lake` directory of the `v1.0` build copied copy-on-write (Mathlib reused from
cache, the six `k = 2` modules replayed, not recompiled):

* `lake build ChowCone.K4.Certificate`, which builds the nine `K4` modules (`CascadeOrigins`,
  `CascadeSizes`, `SquareCharges`, `SignedFlow`, `Rerouting`, `Evaluation`, `Nonnegativity`,
  `UniformFlow`, `Certificate`): all nine were built from source; "Build completed
  successfully (8669 jobs)". No warning from them.
* `lake env lean` on each of the nine files: no output, exit status 0.
* `lake env lean K4AxiomCheck.lean`: output in `lean/K4AxiomCheck.txt`. All 164 declarations
  depend only on `propext`, `Classical.choice`, `Quot.sound`, or a subset of these.
* `lake build`: "Build completed successfully (8662 jobs)", with the same seven linter
  warnings in the `k = 2` files that `RELEASE_CHECKS.md` lists. `lake env lean AxiomCheck.lean`
  reproduces `lean/AxiomCheck.txt` exactly.
* No `sorry`, `admit`, `axiom`, `native_decide`, `skipKernelTC`, `implemented_by`,
  `@[extern]` or `unsafe` in `lean/ChowCone*`, `lean/AxiomCheck.lean` or
  `lean/K4AxiomCheck.lean`.
* `python3 -m pytest tests/`: 509 passed. No Python file has changed since `v1.0`.

The new modules are not imported by `lean/ChowCone.lean`, which is unchanged. The default
`lake build` therefore does not compile them; use `lake build ChowCone.K4.Certificate`.

Review: the correspondence between the Lean definitions and the manuscript was written by the
AI assistant that wrote the proofs. At `v1.1` it was reviewed by five further sessions of the
same AI system (eighth section). It has not been reviewed by a person.

Dependencies. `CascadeOrigins` imports `ChowCone.Flow` (hence `ChowCone.Basic` and Mathlib);
from the `k = 2` project it uses `Supp`, `splitAt`, `indN`, `decomp_at` and
`length_take_of_lt`, and from Mathlib list lemmas, `Finset` sums, and `Composition` only to
prove that the set of sources at a given size is finite. `CascadeSizes` imports
`CascadeOrigins` and `ChowCone.Ratios`, and uses `G`, `gprod`, `blockTerm`, `lastPart` and
their lemmas. `SquareCharges` imports `CascadeOrigins` only. `SignedFlow` imports
`ChowCone.Main` and `CascadeSizes`, and uses `F`, `flowDiv`, `mergeAt` and the lemmas on merges
and sums of `Divergence.lean` and `Main.lean`. `Rerouting` imports `SignedFlow` and
`SquareCharges`, and uses `splitAt_inversion` and `splitAt_mergeAt`. `Evaluation` imports
`Rerouting`. `Nonnegativity` imports `Evaluation`, and uses `G_nonneg`, `Supp_splitAt`,
`mem_le_sum`, `p_mem_splitAt` and `rest_mem_splitAt`. `UniformFlow` imports `Nonnegativity`,
and uses `G_eq_zero_of_one_mem` and `U`. `Certificate` imports `UniformFlow`, and uses
`fEdge`, `splitAt_valid_of_pos`, `comp_blocks_pos`, `comp_length_le`, `comp_getD_le` of
`ChowCone.Main` and `flow_identity`, `flow_nonneg_combination` of `ChowCone.Abstract`.
