import ConnesWeilRH.Dev.C1RouteAEndpointLeftNorms2544
import ConnesWeilRH.Dev.C1RouteAEndpointRightNorms2544

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def fourthCellTerm2544 (i : Fin 30) : ℝ :=
  weightedFamilyCellUpper2538 4 1 (1/2) (nodeModulation2541 i) (storedWidth i ^ 2)
    (cellNearAbs2538 endpointLeftPosition2544 endpointRightPosition2544 / (storedWidth i ^ 2))
    (min (max |endpointLeftPosition2544| |endpointRightPosition2544|) (storedWidth i ^ 2) /
      (storedWidth i ^ 2)) endpointLeftPosition2544 endpointRightPosition2544

noncomputable def thirdCellTerm2544 (i : Fin 30) : ℝ :=
  max (endpointLeftNormUpper2544 i) (endpointRightNormUpper2544 i) +
    fourthCellTerm2544 i * ((endpointRightPosition2544 - endpointLeftPosition2544)/2)

theorem thirdCellTerm_bounds2544 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      endpointLeftPosition2544 endpointRightPosition2544 ≤ thirdCellTerm2544 i := by
  have hi : cellNearAbs2538 endpointLeftPosition2544 endpointRightPosition2544 <
      storedWidth i ^ 2 := by
    fin_cases i <;>
      norm_num [cellNearAbs2538, endpointLeftPosition2544, endpointRightPosition2544, storedWidth]
  unfold weightedFamilyThirdCellUpper2538
  rw [if_pos hi]
  unfold thirdCellTerm2544 fourthCellTerm2544
  apply add_le_add (max_le_max ?_ ?_) (le_refl _)
  · simpa only [weightedUnitJet2539] using endpointLeftNormBound2544 i
  · simpa only [weightedUnitJet2539] using endpointRightNormBound2544 i

noncomputable def thirdAggregateUpper2544 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) * thirdCellTerm2544 i

theorem thirdAggregate_bounds2544 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 endpointLeftPosition2544 endpointRightPosition2544 ≤
        thirdAggregateUpper2544 := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left (thirdCellTerm_bounds2544 i)
  exact add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])

theorem curvature_after_endpoints2544 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 endpointLeftPosition2544 endpointRightPosition2544 ≤
        signedMidpointUpper2543 + thirdAggregateUpper2544 *
          ((endpointRightPosition2544 - endpointLeftPosition2544)/2) := by
  have hm : (endpointLeftPosition2544 + endpointRightPosition2544)/2 =
      midpointPosition2543 := by
    norm_num [endpointLeftPosition2544, endpointRightPosition2544, midpointPosition2543]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add signedMidpointUpper_le2543
  apply mul_le_mul_of_nonneg_right thirdAggregate_bounds2544
  norm_num [endpointLeftPosition2544, endpointRightPosition2544]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.thirdCellTerm_bounds2544
#print axioms ConnesWeilRH.Dev.thirdAggregate_bounds2544
#print axioms ConnesWeilRH.Dev.curvature_after_endpoints2544
