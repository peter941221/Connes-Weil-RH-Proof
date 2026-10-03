import ConnesWeilRH.Dev.C1RouteABatchC05119PlusFourth2559
import ConnesWeilRH.Dev.C1RouteABatchC05119PlusLeftBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05119PlusRightBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05119PlusMidpointBounds2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05119PlusThirdCell2559 (i : Fin 30) : ℝ :=
  max (batchC05119PlusLeftNormUpper2559 i) (batchC05119PlusRightNormUpper2559 i) +
    batchC05119PlusFourthUpper2559 i * ((batchN05120PlusPosition2559 -
        batchN05119PlusPosition2559) / 2)

theorem batchC05119PlusThirdCell_bound2559 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN05119PlusPosition2559 batchN05120PlusPosition2559 ≤ batchC05119PlusThirdCell2559 i :=
          by
  have hh : 0 ≤ (batchN05120PlusPosition2559 - batchN05119PlusPosition2559) / 2 := by
    norm_num [batchN05120PlusPosition2559, batchN05119PlusPosition2559]
  have hf := batchC05119PlusFourthBound2559 i
  unfold weightedFamilyThirdCellUpper2538 batchC05119PlusThirdCell2559
  by_cases hi : cellNearAbs2538 batchN05119PlusPosition2559 batchN05120PlusPosition2559 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC05119PlusFourthCell2559 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC05119PlusLeftNormBound2559 i
    · simpa only [weightedUnitJet2539] using batchC05119PlusRightNormBound2559 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC05119PlusLeftNormUpper2559 i := (norm_nonneg _).trans
        (batchC05119PlusLeftNormBound2559 i)
    unfold batchC05119PlusFourthCell2559 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC05119PlusThirdAggregate2559 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05119PlusThirdCell2559 i

theorem batchC05119PlusThirdAggregate_bound2559 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119PlusPosition2559 batchN05120PlusPosition2559 ≤
          batchC05119PlusThirdAggregate2559 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC05119PlusThirdCell_bound2559 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC05119PlusCurvature_bound2559 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05119PlusPosition2559 batchN05120PlusPosition2559 ≤
        batchC05119PlusSignedMidpointUpper2559 + batchC05119PlusThirdAggregate2559 *
          ((batchN05120PlusPosition2559 - batchN05119PlusPosition2559) / 2) := by
  have hm : (batchN05119PlusPosition2559 + batchN05120PlusPosition2559) / 2 =
      batchC05119PlusMidpointPosition2559 := by
    norm_num [batchN05119PlusPosition2559, batchN05120PlusPosition2559,
        batchC05119PlusMidpointPosition2559]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC05119PlusSignedMidpointUpper_le2559
  apply mul_le_mul_of_nonneg_right batchC05119PlusThirdAggregate_bound2559
  norm_num [batchN05120PlusPosition2559, batchN05119PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119PlusThirdCell_bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusThirdAggregate_bound2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusCurvature_bound2559
