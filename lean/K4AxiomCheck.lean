import ChowCone.K4.CascadeOrigins
import ChowCone.K4.CascadeSizes
import ChowCone.K4.SquareCharges
import ChowCone.K4.SignedFlow
import ChowCone.K4.Rerouting

open ChowCone.K4

-- The public result.
#print axioms cascade_charge_origins

-- Load-bearing lemmas.
#print axioms cascade_getElem?
#print axioms cascade_stage_iff
#print axioms cascade_length
#print axioms cascade_nodup
#print axioms chargeAt_injective
#print axioms eq_append_replicate_iff
#print axioms exists_eq_append_replicate_iff
#print axioms trace_stage_eq_chargeAt_iff
#print axioms origin_trace
#print axioms origin_valid
#print axioms origin_injective
#print axioms chargeAt_mem_trace_iff
#print axioms count_trace_eq_count_origins
#print axioms sum_count_trace
#print axioms validSources_finite
#print axioms total_multiplicity
#print axioms mem_trace_iff
#print axioms leftF2_three_not_charged
#print axioms label_s_of_mem_trace

-- Fidelity of the definitions to the manuscript.
#print axioms selected_finalRight_F4_iff
#print axioms Source.occ_injective
#print axioms Source.leftOcc_child_eq_iff
#print axioms chargeAt_selected
#print axioms indN_leftF2
#print axioms chargeAt_child
#print axioms stage_edge
#print axioms Z_eq_X_succ
#print axioms W_eq_Y_succ
#print axioms sqX_eq_splitAt_source
#print axioms sqY_eq_splitAt_source_child
#print axioms sqW_eq_splitAt_sqZ
#print axioms sqZ_ne_sqY

-- Sizes of the charges and the bounds of Lemma 8.1 (CascadeSizes).
#print axioms r_succ
#print axioms sum_r_le
#print axioms sum_r_three_le
#print axioms G_sqY_eq_sqZ
#print axioms G_source_child_eq
#print axioms rawDebit_origin
#print axioms total_charge
#print axioms total_charge_le
#print axioms total_charge_F3_lt

-- Origins of the charges of rows 1-3 (SquareCharges).
#print axioms selected_left_F4_iff
#print axioms LeftSource.occ_child
#print axioms LeftSource.row1Label_child
#print axioms LeftSource.row2Label_parent
#print axioms LeftSource.row2Label_child
#print axioms LeftSource.square_closes
#print axioms Source.row3Label_child
#print axioms LeftSource.row1Label_selected
#print axioms LeftSource.row2Label_selected
#print axioms Source.row3Label_selected
#print axioms LeftSource.count_row1
#print axioms LeftSource.count_row2
#print axioms Source.count_row3
#print axioms row1_origin_exists_iff
#print axioms row2_origin_exists_iff
#print axioms row3_origin_exists_iff
#print axioms top_origin_unique

-- The signed flow f_0 and its divergence (SignedFlow).
#print axioms signed_flow_divergence
#print axioms divOf_f0
#print axioms divOf_f0_eq
#print axioms primitive_divergences
#print axioms divOf_prim_two
#print axioms divOf_prim_three
#print axioms divOf_prim_four
#print axioms divOf_F2V
#print axioms divOf_wprim
#print axioms outSumOf_wprim
#print axioms inSumOf_wprim
#print axioms ind_merge
#print axioms G_splitAt_nonfinal'
#print axioms G_splitAt_final_left'
#print axioms G_splitAt_final_right'
#print axioms tau_two
#print axioms tau_three
#print axioms tau_four
#print axioms T2_eq
#print axioms Q2_sub_nine_V
#print axioms V_splitAt
#print axioms f0_eq
#print axioms prim_two
#print axioms divOf_F
#print axioms indNs_eq_one_iff
#print axioms indFLs_eq_one_iff
#print axioms indFRs_eq_one_iff
#print axioms w4_eq_U_mul_a4
#print axioms Bd_eq

-- The rerouting and the flow f_d (Rerouting).
#print axioms divOf_fd
#print axioms divOf_fd_eq_divOf_f0
#print axioms divOf_edgeUnit
#print axioms divOf_squareFlow
#print axioms LeftSource.divOf_square
#print axioms Source.divOf_square
#print axioms divOf_cascSquare
#print axioms divOf_cascadeFlow
#print axioms divOf_sum
#print axioms validLeftSources_finite
#print axioms LeftSource.eAB_eq
#print axioms LeftSource.eAC_eq
#print axioms LeftSource.eCD_eq
#print axioms Source.eAB_eq
#print axioms Source.eAC_eq
#print axioms cZW_eq_cXY_next
#print axioms LeftSource.square_supp
#print axioms Source.square_supp
#print axioms cascSquare_supp
