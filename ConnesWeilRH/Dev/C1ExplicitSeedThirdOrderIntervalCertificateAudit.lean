import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate

/-!
# Axiom footprint of the seed third-order interval certificate brick

Focused `#print axioms` for every declaration of
`ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate`. All of them must
depend on exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
open Real
open expNegInvGlue

noncomputable section

open scoped Topology

#print axioms expTaylor
#print axioms expTail
#print axioms expTaylor_nonneg
#print axioms one_le_expTaylor
#print axioms expTail_nonneg
#print axioms expTail_le_one
#print axioms sum_le_exp_20
#print axioms exp_le_sum_add
#print axioms one_add_le_expTaylor
#print axioms expTail_le_self
#print axioms one_le_expTaylor_sub_expTail
#print axioms exp_bounds_pow
#print axioms seedV
#print axioms seedU
#print axioms seedV_pos
#print axioms seedV_nonneg
#print axioms seedV_mono
#print axioms seedU_eq_reflect
#print axioms ratio_mono
#print axioms seedU_le_one
#print axioms seedU_nonneg
#print axioms seedU_monoOn_Ioo
#print axioms seedULower_cheap
#print axioms seedExpLo
#print axioms seedExpHi
#print axioms seedULo
#print axioms seedUHi
#print axioms seedULo_zero
#print axioms seedU_mem_Icc
#print axioms seedExpLo_ge_one
#print axioms seedExpHi_nonneg
#print axioms seedULo_nonneg
#print axioms thirdOrderMiddle_eq_expansion
#print axioms thirdOrderConstant_eq_expansion
#print axioms thirdOrderLeading_le_of_le
#print axioms thirdOrderMiddle_mem_Icc
#print axioms thirdOrderConstant_mem_Icc
#print axioms seedBracket
#print axioms seedBracketLower
#print axioms seedBracketUpper
#print axioms seedBracket_mem_Icc
#print axioms seedU_zero
#print axioms seedU_sandwich_exp
#print axioms seedU_sandwich_zero
#print axioms seedU_sandwich_one
#print axioms seedBracket_neg_L01
#print axioms seedBracket_neg_L02
#print axioms seedBracket_neg_L03
#print axioms seedBracket_neg_L04
#print axioms seedBracket_neg_L05
#print axioms seedBracket_neg_L06
#print axioms seedBracket_neg_L07
#print axioms seedBracket_neg_L08
#print axioms seedBracket_neg_L09
#print axioms seedBracket_neg_L10
#print axioms seedBracket_neg_L11
#print axioms seedBracket_neg_L12
#print axioms seedBracket_neg_L13
#print axioms seedBracket_neg_L14
#print axioms seedBracket_neg_L15
#print axioms seedBracket_neg_L16
#print axioms seedBracket_neg_L17
#print axioms seedBracket_neg_L18
#print axioms seedBracket_neg_L19
#print axioms seedBracket_neg_L20
#print axioms seedBracket_neg_L21
#print axioms seedBracket_neg_L22
#print axioms seedBracket_pos_R01
#print axioms seedBracket_pos_R02
#print axioms seedBracket_pos_R03
#print axioms seedBracket_pos_R04
#print axioms seedBracket_pos_R05
#print axioms seedBracket_pos_R06
#print axioms seedBracket_pos_R07
#print axioms seedBracket_pos_R08
#print axioms seedBracket_pos_R09
#print axioms seedBracket_pos_R10
#print axioms seedBracket_pos_R11
#print axioms seedBracket_pos_R12
#print axioms seedBracket_pos_R13
#print axioms seedBracket_pos_R14
#print axioms seedBracket_pos_R15
#print axioms seedVSlope
#print axioms seedAlphaSlope
#print axioms seedBetaSlope
#print axioms seedGammaSlope
#print axioms hasDerivAt_seedV
#print axioms hasDerivAt_seedU
#print axioms seedHprime
#print axioms hasDerivAt_seedBracket
#print axioms seedAlphaSlope_le
#print axioms seedBetaSlope_le
#print axioms thirdOrderMiddle_le
#print axioms seedGammaSlope_le
#print axioms seedVSlope_le
#print axioms seedBracket_neg_of_Icc_zero_s_lo
#print axioms seedBracket_pos_of_Ico_s_hi_one
#print axioms seedUHi_le_one
#print axioms seedUHi_ge_neg_one
#print axioms seedHprimeLower
#print axioms seedHprimeLower_pos
#print axioms seedHprime_ge_lower
#print axioms continuousOn_seedBracket
#print axioms seedBracket_strictMonoOn
#print axioms seedBracket_at_s_lo_neg
#print axioms seedBracket_at_s_hi_pos
#print axioms seedBracket_at_s_d_neg
#print axioms seedBracket_at_s_c_pos
#print axioms exists_seedBracket_eq_zero
#print axioms existsUnique_seedBracket_eq_zero
#print axioms seedBracket_neg_of_Icc_zero_s_d
#print axioms seedBracket_pos_of_Ico_s_c_one
#print axioms iteratedDeriv_three_smoothTransition_eq_seedBracket
#print axioms iteratedDeriv_three_smoothTransition_seedBracket_pos_iff
#print axioms iteratedDeriv_three_smoothTransition_seedBracket_neg_iff
#print axioms iteratedDeriv_three_pos_of_Ioc_zero_x_c
#print axioms iteratedDeriv_three_neg_of_Ico_x_d_half
#print axioms iteratedDeriv_three_nonneg_of_Icc_zero_x_c
#print axioms iteratedDeriv_three_nonpos_of_Icc_x_d_half
#print axioms gainStd
#print axioms gainSlopeStd
#print axioms seedP
#print axioms ttwoMp
#print axioms ttwoLower
#print axioms ttwoUpper
#print axioms gapLo
#print axioms gapHi
#print axioms gapBound
#print axioms iteratedDeriv_two_smoothTransition_mem_Icc
#print axioms iteratedDeriv_three_abs_le_gapBound
#print axioms derivOrderL1_smoothSeed_three_mem_Icc

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
