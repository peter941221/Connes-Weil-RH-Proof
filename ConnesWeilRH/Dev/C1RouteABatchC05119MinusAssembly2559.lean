import ConnesWeilRH.Dev.C1RouteABatchC05119MinusFourth2559
import ConnesWeilRH.Dev.C1RouteABatchC05119MinusLeftBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05119MinusRightBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05119MinusMidpointBounds2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05119MinusThirdCell2559 (i : Fin 30) : ℝ :=
  max (batchC05119MinusLeftNormUpper2559 i) (batchC05119MinusRightNormUpper2559 i) +
    batchC05119MinusFourthUpper2559 i * ((batchN05120MinusPosition2559 -
        batchN05119MinusPosition2559) / 2)

theorem batchC05119MinusThirdCell_bound2559 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (-1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN05119MinusPosition2559 batchN05120MinusPosition2559 ≤ batchC05119MinusThirdCell2559 i
          := by
  have hh : 0 ≤ (batchN05120MinusPosition2559 - batchN05119MinusPosition2559) / 2 := by
    norm_num [batchN05120MinusPosition2559, batchN05119MinusPosition2559]
  have hf := batchC05119MinusFourthBound2559 i
  unfold weightedFamilyThirdCellUpper2538 batchC05119MinusThirdCell2559
  by_cases hi : cellNearAbs2538 batchN05119MinusPosition2559 batchN05120MinusPosition2559 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC05119MinusFourthCell2559 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC05119MinusLeftNormBound2559 i
    · simpa only [weightedUnitJet2539] using batchC05119MinusRightNormBound2559 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC05119MinusLeftNormUpper2559 i := (norm_nonneg _).trans
        (batchC05119MinusLeftNormBound2559 i)
    unfold batchC05119MinusFourthCell2559 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC05119MinusThirdAggregate2559 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05119MinusThirdCell2559 i

theorem batchC05119MinusThirdAggregate_bound2559 :
    signedThirdCellUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119MinusPosition2559 batchN05120MinusPosition2559 ≤
          batchC05119MinusThirdAggregate2559 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC05119MinusThirdCell_bound2559 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC05119MinusCurvature_bound2559 :
    signedCurvatureUpper2539 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119MinusPosition2559 batchN05120MinusPosition2559 ≤
        batchC05119MinusSignedMidpointUpper2559 + batchC05119MinusThirdAggregate2559 *
          ((batchN05120MinusPosition2559 - batchN05119MinusPosition2559) / 2) := by
  have hm : (batchN05119MinusPosition2559 + batchN05120MinusPosition2559) / 2 =
      batchC05119MinusMidpointPosition2559 := by
    norm_num [batchN05119MinusPosition2559, batchN05120MinusPosition2559,
        batchC05119MinusMidpointPosition2559]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC05119MinusSignedMidpointUpper_le2559
  apply mul_le_mul_of_nonneg_right batchC05119MinusThirdAggregate_bound2559
  norm_num [batchN05120MinusPosition2559, batchN05119MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusThirdCell_bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusThirdAggregate_bound2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusCurvature_bound2559
