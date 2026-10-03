import ConnesWeilRH.Dev.C1RouteABatchC05120MinusFourth2559
import ConnesWeilRH.Dev.C1RouteABatchC05120MinusLeftBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05120MinusRightBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05120MinusMidpointBounds2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05120MinusThirdCell2559 (i : Fin 30) : ℝ :=
  max (batchC05120MinusLeftNormUpper2559 i) (batchC05120MinusRightNormUpper2559 i) +
    batchC05120MinusFourthUpper2559 i * ((batchN05121MinusPosition2559 -
        batchN05120MinusPosition2559) / 2)

theorem batchC05120MinusThirdCell_bound2559 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (-1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN05120MinusPosition2559 batchN05121MinusPosition2559 ≤ batchC05120MinusThirdCell2559 i
          := by
  have hh : 0 ≤ (batchN05121MinusPosition2559 - batchN05120MinusPosition2559) / 2 := by
    norm_num [batchN05121MinusPosition2559, batchN05120MinusPosition2559]
  have hf := batchC05120MinusFourthBound2559 i
  unfold weightedFamilyThirdCellUpper2538 batchC05120MinusThirdCell2559
  by_cases hi : cellNearAbs2538 batchN05120MinusPosition2559 batchN05121MinusPosition2559 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC05120MinusFourthCell2559 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC05120MinusLeftNormBound2559 i
    · simpa only [weightedUnitJet2539] using batchC05120MinusRightNormBound2559 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC05120MinusLeftNormUpper2559 i := (norm_nonneg _).trans
        (batchC05120MinusLeftNormBound2559 i)
    unfold batchC05120MinusFourthCell2559 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC05120MinusThirdAggregate2559 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05120MinusThirdCell2559 i

theorem batchC05120MinusThirdAggregate_bound2559 :
    signedThirdCellUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05120MinusPosition2559 batchN05121MinusPosition2559 ≤
          batchC05120MinusThirdAggregate2559 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC05120MinusThirdCell_bound2559 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC05120MinusCurvature_bound2559 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05120MinusPosition2559 batchN05121MinusPosition2559 ≤
        batchC05120MinusSignedMidpointUpper2559 + batchC05120MinusThirdAggregate2559 *
          ((batchN05121MinusPosition2559 - batchN05120MinusPosition2559) / 2) := by
  have hm : (batchN05120MinusPosition2559 + batchN05121MinusPosition2559) / 2 =
      batchC05120MinusMidpointPosition2559 := by
    norm_num [batchN05120MinusPosition2559, batchN05121MinusPosition2559,
        batchC05120MinusMidpointPosition2559]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC05120MinusSignedMidpointUpper_le2559
  apply mul_le_mul_of_nonneg_right batchC05120MinusThirdAggregate_bound2559
  norm_num [batchN05121MinusPosition2559, batchN05120MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusThirdCell_bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusThirdAggregate_bound2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusCurvature_bound2559
