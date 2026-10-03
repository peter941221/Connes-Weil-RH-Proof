import ConnesWeilRH.Dev.C1RouteABatchC02701MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02701MinusLeftBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02701MinusRightBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02701MinusMidpointBounds2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02701MinusThirdCell2558 (i : Fin 30) : ℝ :=
  max (batchC02701MinusLeftNormUpper2558 i) (batchC02701MinusRightNormUpper2558 i) +
    batchC02701MinusFourthUpper2558 i * ((batchN02702MinusPosition2558 -
        kernelN02701MinusPosition2555) / 2)

theorem batchC02701MinusThirdCell_bound2558 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (-1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      kernelN02701MinusPosition2555 batchN02702MinusPosition2558 ≤ batchC02701MinusThirdCell2558 i
          := by
  have hh : 0 ≤ (batchN02702MinusPosition2558 - kernelN02701MinusPosition2555) / 2 := by
    norm_num [batchN02702MinusPosition2558, kernelN02701MinusPosition2555]
  have hf := batchC02701MinusFourthBound2558 i
  unfold weightedFamilyThirdCellUpper2538 batchC02701MinusThirdCell2558
  by_cases hi : cellNearAbs2538 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC02701MinusFourthCell2558 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC02701MinusLeftNormBound2558 i
    · simpa only [weightedUnitJet2539] using batchC02701MinusRightNormBound2558 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC02701MinusLeftNormUpper2558 i := (norm_nonneg _).trans
        (batchC02701MinusLeftNormBound2558 i)
    unfold batchC02701MinusFourthCell2558 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC02701MinusThirdAggregate2558 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02701MinusThirdCell2558 i

theorem batchC02701MinusThirdAggregate_bound2558 :
    signedThirdCellUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 ≤
          batchC02701MinusThirdAggregate2558 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02701MinusThirdCell_bound2558 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC02701MinusCurvature_bound2558 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02701MinusPosition2555 batchN02702MinusPosition2558 ≤
        batchC02701MinusSignedMidpointUpper2558 + batchC02701MinusThirdAggregate2558 *
          ((batchN02702MinusPosition2558 - kernelN02701MinusPosition2555) / 2) := by
  have hm : (kernelN02701MinusPosition2555 + batchN02702MinusPosition2558) / 2 =
      batchC02701MinusMidpointPosition2558 := by
    norm_num [kernelN02701MinusPosition2555, batchN02702MinusPosition2558,
        batchC02701MinusMidpointPosition2558]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC02701MinusSignedMidpointUpper_le2558
  apply mul_le_mul_of_nonneg_right batchC02701MinusThirdAggregate_bound2558
  norm_num [batchN02702MinusPosition2558, kernelN02701MinusPosition2555]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02701MinusThirdCell_bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusThirdAggregate_bound2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusCurvature_bound2558
