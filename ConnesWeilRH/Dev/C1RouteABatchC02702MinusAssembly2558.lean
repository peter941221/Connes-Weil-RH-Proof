import ConnesWeilRH.Dev.C1RouteABatchC02702MinusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02702MinusLeftBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02702MinusRightBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02702MinusMidpointBounds2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02702MinusThirdCell2558 (i : Fin 30) : ℝ :=
  max (batchC02702MinusLeftNormUpper2558 i) (batchC02702MinusRightNormUpper2558 i) +
    batchC02702MinusFourthUpper2558 i * ((batchN02703MinusPosition2558 -
        batchN02702MinusPosition2558) / 2)

theorem batchC02702MinusThirdCell_bound2558 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (-1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN02702MinusPosition2558 batchN02703MinusPosition2558 ≤ batchC02702MinusThirdCell2558 i
          := by
  have hh : 0 ≤ (batchN02703MinusPosition2558 - batchN02702MinusPosition2558) / 2 := by
    norm_num [batchN02703MinusPosition2558, batchN02702MinusPosition2558]
  have hf := batchC02702MinusFourthBound2558 i
  unfold weightedFamilyThirdCellUpper2538 batchC02702MinusThirdCell2558
  by_cases hi : cellNearAbs2538 batchN02702MinusPosition2558 batchN02703MinusPosition2558 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC02702MinusFourthCell2558 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC02702MinusLeftNormBound2558 i
    · simpa only [weightedUnitJet2539] using batchC02702MinusRightNormBound2558 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC02702MinusLeftNormUpper2558 i := (norm_nonneg _).trans
        (batchC02702MinusLeftNormBound2558 i)
    unfold batchC02702MinusFourthCell2558 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC02702MinusThirdAggregate2558 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02702MinusThirdCell2558 i

theorem batchC02702MinusThirdAggregate_bound2558 :
    signedThirdCellUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02702MinusPosition2558 batchN02703MinusPosition2558 ≤
          batchC02702MinusThirdAggregate2558 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02702MinusThirdCell_bound2558 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC02702MinusCurvature_bound2558 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02702MinusPosition2558 batchN02703MinusPosition2558 ≤
        batchC02702MinusSignedMidpointUpper2558 + batchC02702MinusThirdAggregate2558 *
          ((batchN02703MinusPosition2558 - batchN02702MinusPosition2558) / 2) := by
  have hm : (batchN02702MinusPosition2558 + batchN02703MinusPosition2558) / 2 =
      batchC02702MinusMidpointPosition2558 := by
    norm_num [batchN02702MinusPosition2558, batchN02703MinusPosition2558,
        batchC02702MinusMidpointPosition2558]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC02702MinusSignedMidpointUpper_le2558
  apply mul_le_mul_of_nonneg_right batchC02702MinusThirdAggregate_bound2558
  norm_num [batchN02703MinusPosition2558, batchN02702MinusPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusThirdCell_bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusThirdAggregate_bound2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusCurvature_bound2558
