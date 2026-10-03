import ConnesWeilRH.Dev.C1RouteABatchC02700MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02700MinusLeftBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02700MinusRightBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02700MinusMidpointBounds2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02700MinusThirdCell2558 (i : Fin 30) : ℝ :=
  max (batchC02700MinusLeftNormUpper2558 i) (batchC02700MinusRightNormUpper2558 i) +
    batchC02700MinusFourthUpper2558 i * ((kernelN02701MinusPosition2555 -
        kernelN02700MinusPosition2555) / 2)

theorem batchC02700MinusThirdCell_bound2558 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (-1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 ≤ batchC02700MinusThirdCell2558
          i := by
  have hh : 0 ≤ (kernelN02701MinusPosition2555 - kernelN02700MinusPosition2555) / 2 := by
    norm_num [kernelN02701MinusPosition2555, kernelN02700MinusPosition2555]
  have hf := batchC02700MinusFourthBound2558 i
  unfold weightedFamilyThirdCellUpper2538 batchC02700MinusThirdCell2558
  by_cases hi : cellNearAbs2538 kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC02700MinusFourthCell2558 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC02700MinusLeftNormBound2558 i
    · simpa only [weightedUnitJet2539] using batchC02700MinusRightNormBound2558 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC02700MinusLeftNormUpper2558 i := (norm_nonneg _).trans
        (batchC02700MinusLeftNormBound2558 i)
    unfold batchC02700MinusFourthCell2558 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC02700MinusThirdAggregate2558 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02700MinusThirdCell2558 i

theorem batchC02700MinusThirdAggregate_bound2558 :
    signedThirdCellUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 ≤
          batchC02700MinusThirdAggregate2558 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02700MinusThirdCell_bound2558 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC02700MinusCurvature_bound2558 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 kernelN02700MinusPosition2555 kernelN02701MinusPosition2555 ≤
        batchC02700MinusSignedMidpointUpper2558 + batchC02700MinusThirdAggregate2558 *
          ((kernelN02701MinusPosition2555 - kernelN02700MinusPosition2555) / 2) := by
  have hm : (kernelN02700MinusPosition2555 + kernelN02701MinusPosition2555) / 2 =
      batchC02700MinusMidpointPosition2558 := by
    norm_num [kernelN02700MinusPosition2555, kernelN02701MinusPosition2555,
        batchC02700MinusMidpointPosition2558]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC02700MinusSignedMidpointUpper_le2558
  apply mul_le_mul_of_nonneg_right batchC02700MinusThirdAggregate_bound2558
  norm_num [kernelN02701MinusPosition2555, kernelN02700MinusPosition2555]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700MinusThirdCell_bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusThirdAggregate_bound2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusCurvature_bound2558
