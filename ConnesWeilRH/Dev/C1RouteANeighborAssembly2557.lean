import ConnesWeilRH.Dev.C1RouteANeighborFourth2557
import ConnesWeilRH.Dev.C1RouteANeighborLeftBounds2557
import ConnesWeilRH.Dev.C1RouteANeighborRightBounds2557
import ConnesWeilRH.Dev.C1RouteANeighborMidpointBounds2557

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def neighborThirdCell2557 (i : Fin 30) : ℝ :=
  max (neighborLeftNormUpper2557 i) (neighborRightNormUpper2557 i) +
    neighborFourthUpper2557 i * ((neighborRightPosition2557 - kernelN02701PlusPosition2555) / 2)

theorem neighborThirdCell_bound2557 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      kernelN02701PlusPosition2555 neighborRightPosition2557 ≤ neighborThirdCell2557 i := by
  have hh : 0 ≤ (neighborRightPosition2557 - kernelN02701PlusPosition2555) / 2 := by
    norm_num [neighborRightPosition2557, kernelN02701PlusPosition2555]
  have hf := neighborFourthBound2557 i
  unfold weightedFamilyThirdCellUpper2538 neighborThirdCell2557
  by_cases hi : cellNearAbs2538 kernelN02701PlusPosition2555 neighborRightPosition2557 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold neighborFourthCell2557 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using neighborLeftNormBound2557 i
    · simpa only [weightedUnitJet2539] using neighborRightNormBound2557 i
  · rw [if_neg hi]
    have hl : 0 ≤ neighborLeftNormUpper2557 i := (norm_nonneg _).trans (neighborLeftNormBound2557
        i)
    unfold neighborFourthCell2557 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def neighborThirdAggregate2557 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      neighborThirdCell2557 i

theorem neighborThirdAggregate_bound2557 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701PlusPosition2555 neighborRightPosition2557 ≤
          neighborThirdAggregate2557 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (neighborThirdCell_bound2557 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem neighborCurvature_bound2557 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701PlusPosition2555 neighborRightPosition2557 ≤
        neighborSignedMidpointUpper2557 + neighborThirdAggregate2557 *
          ((neighborRightPosition2557 - kernelN02701PlusPosition2555) / 2) := by
  have hm : (kernelN02701PlusPosition2555 + neighborRightPosition2557) / 2 =
      neighborMidpointPosition2557 := by
    norm_num [kernelN02701PlusPosition2555, neighborRightPosition2557,
        neighborMidpointPosition2557]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add neighborSignedMidpointUpper_le2557
  apply mul_le_mul_of_nonneg_right neighborThirdAggregate_bound2557
  norm_num [neighborRightPosition2557, kernelN02701PlusPosition2555]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborThirdCell_bound2557
#print axioms ConnesWeilRH.Dev.neighborThirdAggregate_bound2557
#print axioms ConnesWeilRH.Dev.neighborCurvature_bound2557
