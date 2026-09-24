import ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass

/-!
# Axiom footprint of the seed second-order mass brick

Focused `#print axioms` for every declaration of
`ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass`. All of them must depend on
exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
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

#print axioms deriv_smoothTransition_eq_mul_windowGain
#print axioms deriv_smoothTransition_zero
#print axioms windowGain_one_sub
#print axioms windowGainSlope_one_sub
#print axioms hasDerivAt_windowGain
#print axioms one_sub_two_mul_smoothTransition_eq
#print axioms exp_neg_sub_one_div_exp_neg_add_one
#print axioms self_div_add_two_le_exp_ratio
#print axioms windowGain_ratio_lt_exp_ratio
#print axioms iteratedDeriv_two_smoothTransition_eq_deriv_deriv
#print axioms iteratedDeriv_two_smoothTransition_eq
#print axioms windowGain_half_eq
#print axioms windowGainSlope_half_eq
#print axioms windowGainSlope_div_sq_half_eq
#print axioms halfPoint_one_sub_two_div
#print axioms reflectPoint_one_sub_two_div
#print axioms iteratedDeriv_two_smoothTransition_zero
#print axioms iteratedDeriv_two_smoothTransition_one
#print axioms iteratedDeriv_two_smoothTransition_half
#print axioms iteratedDeriv_two_smoothTransition_nonneg
#print axioms iteratedDeriv_two_smoothTransition_nonpos
#print axioms integral_abs_iteratedDeriv_two_smoothTransition_left
#print axioms integral_abs_iteratedDeriv_two_smoothTransition_right
#print axioms integral_iteratedDeriv_two_smoothTransition_left
#print axioms integral_iteratedDeriv_two_smoothTransition_right
#print axioms integral_abs_iteratedDeriv_two_smoothTransition
#print axioms derivOrderL1_smoothSeed_two

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
