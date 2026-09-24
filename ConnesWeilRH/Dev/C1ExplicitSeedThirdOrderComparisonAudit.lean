import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderComparison

/-!
# Axiom footprint of the seed third-order sign comparison brick

Focused `#print axioms` for every declaration of
`ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderComparison`. All of them must depend
on exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
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

#print axioms windowGain_reflect_eq
#print axioms windowGainSlope_reflect_eq
#print axioms windowGainSecondSlope_standard_eq
#print axioms windowGainSecondSlope_reflect_eq
#print axioms one_sub_two_mul_smoothTransition_reflect_eq
#print axioms one_sub_two_mul_smoothTransition_reflect_pos
#print axioms thirdOrderBracket
#print axioms thirdOrderLeading
#print axioms thirdOrderMiddle
#print axioms thirdOrderConstant
#print axioms thirdOrderBracket_eq_quadratic
#print axioms thirdOrderLeading_pos
#print axioms thirdOrderMiddle_nonneg
#print axioms thirdOrderConstant_neg
#print axioms bracket_clearing
#print axioms iteratedDeriv_three_smoothTransition_eq_bracket
#print axioms quadratic_discriminant_identity
#print axioms mul_neg_of_pos_left_iff
#print axioms middle_lt_sqrt
#print axioms quadratic_neg_iff
#print axioms quadratic_pos_iff
#print axioms thirdOrderThreshold
#print axioms thirdOrderThreshold_pos
#print axioms iteratedDeriv_three_smoothTransition_sign_iff
#print axioms iteratedDeriv_three_smoothTransition_neg_iff

end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
