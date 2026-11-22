import ChowCone.K4.CascadeOrigins
import ChowCone.K4.CascadeSizes

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
