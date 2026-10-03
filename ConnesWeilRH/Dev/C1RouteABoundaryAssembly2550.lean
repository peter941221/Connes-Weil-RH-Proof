import ConnesWeilRH.Dev.C1RouteABoundaryFourth2550
import ConnesWeilRH.Dev.C1RouteABoundaryLeftBounds2549
import ConnesWeilRH.Dev.C1RouteABoundaryRightBounds2549
import ConnesWeilRH.Dev.C1RouteABoundaryMidpointBounds2549

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def edgeThirdCell2550 (i : Fin 30) : ℝ :=
  max (edgeLeftNormUpper2549 i) (edgeRightNormUpper2549 i) +
    edgeFourthUpper2550 i * ((edgeRightPosition2548 - edgeLeftPosition2548) / 2)

theorem edgeThirdCell_bound2550 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      edgeLeftPosition2548 edgeRightPosition2548 ≤ edgeThirdCell2550 i := by
  have hh : 0 ≤ (edgeRightPosition2548 - edgeLeftPosition2548) / 2 := by
    norm_num [edgeRightPosition2548, edgeLeftPosition2548]
  have hf := edgeFourthBound2550 i
  unfold weightedFamilyThirdCellUpper2538 edgeThirdCell2550
  by_cases hi : cellNearAbs2538 edgeLeftPosition2548 edgeRightPosition2548 < storedWidth i ^ 2
  · rw [if_pos hi]
    unfold edgeFourthCell2550 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using edgeLeftNormBound2549 i
    · simpa only [weightedUnitJet2539] using edgeRightNormBound2549 i
  · rw [if_neg hi]
    have hl : 0 ≤ edgeLeftNormUpper2549 i := (norm_nonneg _).trans (edgeLeftNormBound2549 i)
    unfold edgeFourthCell2550 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def edgeThirdAggregate2550 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) * edgeThirdCell2550 i

theorem edgeThirdAggregate_bound2550 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeLeftPosition2548 edgeRightPosition2548 ≤ edgeThirdAggregate2550 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (edgeThirdCell_bound2550 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem edgeCurvature_bound2550 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeLeftPosition2548 edgeRightPosition2548 ≤
        edgeSignedMidpointUpper2549 + edgeThirdAggregate2550 *
          ((edgeRightPosition2548 - edgeLeftPosition2548) / 2) := by
  have hm : (edgeLeftPosition2548 + edgeRightPosition2548) / 2 = edgeMidpointPosition2548 := by
    norm_num [edgeLeftPosition2548, edgeRightPosition2548, edgeMidpointPosition2548]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add edgeSignedMidpointUpper_le2549
  apply mul_le_mul_of_nonneg_right edgeThirdAggregate_bound2550
  norm_num [edgeRightPosition2548, edgeLeftPosition2548]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.edgeThirdCell_bound2550
#print axioms ConnesWeilRH.Dev.edgeThirdAggregate_bound2550
#print axioms ConnesWeilRH.Dev.edgeCurvature_bound2550
