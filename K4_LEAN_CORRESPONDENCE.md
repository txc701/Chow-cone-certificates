# Lean ⇄ manuscript correspondence, `k = 4`: origins of the cascade charges

First Lean milestone for the fourth-moment certificate. Manuscript:
`CHOW_CONE_FLOWS_MANUSCRIPT.tex` as of 21 November 2026 (release `v1.0`), Section 7,
equations (31)–(33), Lemma 8.1 and Table 1. Lean file:
`lean/ChowCone/K4/CascadeOrigins.lean`, module `ChowCone.K4.CascadeOrigins`, namespace
`ChowCone.K4`. Toolchain and Mathlib are those of the `k = 2` project (Lean `v4.32.2`,
Mathlib `v4.32.2`); nothing in the `k = 2` sources, the manuscript or the toolchain was
changed. This file complements `LEAN_CORRESPONDENCE.md`, which covers `k = 2`.

## What is proved

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
(`Source.rawDebit`). It is not derived from a formal definition of the flow `f_0`, which does
not yet exist in Lean.

## Third milestone: origins of rows 1–3 (`ChowCone.K4.SquareCharges`)

File `lean/ChowCone/K4/SquareCharges.lean`. A *left source* is a tagged nonfinal or final-left
`F_4` occurrence on the block `t + 4` of `A = P.(t+4).S`; it is final-left exactly when `S` is
empty. Its square (28)–(29) charges the left `F_2` occurrence of the block `t + 4` of `A`
(row 1, edge `A → C`) and the left `F_2` occurrence of the block `t + 2` of `C = P.(2,t+2).S`
(row 2, edge `C → D`). The initial square (31) of a final-right source charges the right `F_2`
occurrence of the final block `t + 4` (row 3, edge `A → C = X_0`).

* In each row the charged occurrence determines the origin (`top_origin_unique`), and a source
  charges a label once or not at all (`count_row1`, `count_row2`, `count_row3`).
* An origin exists exactly for: a selected left `F_2` occurrence of a block at least 6
  (row 1); a selected left `F_2` occurrence whose block is immediately preceded by a 2
  (row 2); a selected right `F_2` occurrence of a final block at least 6 (row 3).

The amounts (30) of these charges are not formalized.

## What is not proved


The amounts of the charges of rows 1–3 (equation (30) and the amount of row 3), the
collision and capacity inequalities of Proposition 8.2 beyond the two cascade totals above,
the divergence of the signed flow, the statement that each path square has zero divergence,
and the matroid bridge. No edge flow is defined: the cancellation of a debit by the next
square is represented only by the identification of the edges involved, and the amounts are
the raw debits of the sources. Theorem 9.1 is a later target.

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
* **`d ≥ 3`.** The public theorem takes `d` with `3 ≤ d` and `N = d + 2`. The hypothesis
  `3 ≤ d` is not used: the other hypotheses force `N ≥ 6`, that is `d ≥ 4`. All supporting
  theorems are stated for an arbitrary `N`.
* **Junk values.** `cascade Q 0 = cascade Q 1 = []`. These parameters do not occur for a
  source, since `t ≥ 2` and each stage lowers the parameter by 2 only when it is at least 4.
  `chargeAt Q y` for `y < 2` is the row-4 form and is never used; every theorem that needs
  it assumes `2 ≤ y`.

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
| `LeftSource.row1Label`, `row1Label_parent`, `row1Label_child` | Table 1, row 1 | left `F_2` occurrence of the block `t+4` of `A`; edge `A → C` |
| `LeftSource.row2Label`, `row2Label_parent`, `row2Label_child` | Table 1, row 2 | left `F_2` occurrence of the block `t+2` of `C`; edge `C → D` |
| `LeftSource.occ_child`, `LeftSource.square_closes` | (28) | `B = P.(4,t).S`; `B → D` is the split `4 ↦ (2,2)` |
| `Source.row3Label`, `row3Label_parent`, `row3Label_child` | Table 1, row 3; (31) | right `F_2` occurrence of the final block `t+4`; edge `A → C = X_0` |
| `row1Label_selected`, `row2Label_selected`, `row3Label_selected` | Table 1, "charged occurrence" | the labels are selected `F_2` occurrences |
| `TopRow`, `TopCharge`, `LeftSource.charges`, `Source.topCharges`, `count_row1`, `count_row2`, `count_row3` | Table 1, rows 1–3, "at most one" | each source charges a label once or not at all |
| `row1Label_injective`, `row2Label_injective`, `row3Label_injective`, `top_origin_unique` | "For types 1–3, the charged occurrence and the type determine the origin" | at most one origin |
| `row1_origin_exists_iff`, `row3_origin_exists_iff` | Table 1, rows 1 and 3, "the block is at least 6" | when an origin exists |
| `row2_origin_exists_iff` | Table 1, row 2, "needs the preceding 2"; "recovered by merging the affected block with the 2 immediately preceding it" | when an origin exists |

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

## Verification (2026-11-21 and 2026-11-22)

Run in a worktree of the branch, with the `.lake` directory of the `v1.0` build copied
copy-on-write. Mathlib was reused from cache (`lake build --no-build Mathlib`: "All targets
up-to-date (8654 jobs)"). The six `k = 2` modules were replayed from cache, not recompiled.

* `lake build` of `ChowCone.K4.CascadeOrigins`, `ChowCone.K4.CascadeSizes` and
  `ChowCone.K4.SquareCharges`: the three modules were built from source; "Build completed
  successfully". No warning from the new files.
* `lake env lean` on each of the three files: no output, exit status 0.
* `lake env lean K4AxiomCheck.lean`: output in `lean/K4AxiomCheck.txt`. All 59 declarations
  depend only on `propext`, `Classical.choice`, `Quot.sound`, or a subset of these.
* `lake build`: "Build completed successfully (8662 jobs)", with the same seven linter
  warnings in the `k = 2` files that `RELEASE_CHECKS.md` lists. `lake env lean AxiomCheck.lean`
  reproduces `lean/AxiomCheck.txt` exactly.
* No `sorry`, `admit`, `axiom`, `native_decide`, `skipKernelTC`, `implemented_by`,
  `@[extern]` or `unsafe` in `lean/ChowCone*`, `lean/AxiomCheck.lean` or
  `lean/K4AxiomCheck.lean`.
* `python3 -m pytest tests/` on the first commit of the branch: 509 passed. No Python file
  has changed.

The new modules are not imported by `lean/ChowCone.lean`, which is unchanged. The default
`lake build` therefore does not compile them; use
`lake build ChowCone.K4.CascadeSizes ChowCone.K4.SquareCharges`, which also builds
`ChowCone.K4.CascadeOrigins`.

Dependencies of `CascadeOrigins`: `ChowCone.Flow` (hence `ChowCone.Basic` and Mathlib). From the
`k = 2` project it uses `Supp`, `splitAt`, `indN`, `decomp_at` and `length_take_of_lt`. From
Mathlib it uses list lemmas, `Finset` sums, and `Composition` only to prove that the set of
sources at a given size is finite. `CascadeSizes` imports `CascadeOrigins` and
`ChowCone.Ratios`; from the `k = 2` project it uses `G`, `gprod`, `blockTerm`, `lastPart` and
their lemmas (`G_pos`, `blockTerm_pos`, `blockTerm_two`, `gprod_append`, `gprod_cons`). `SquareCharges` imports `CascadeOrigins` only.
