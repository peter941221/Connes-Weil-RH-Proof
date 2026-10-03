import ConnesWeilRH.Dev.C1RouteABatchC05120PlusFourth2559
import ConnesWeilRH.Dev.C1RouteABatchC05120PlusLeftBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05120PlusRightBounds2559
import ConnesWeilRH.Dev.C1RouteABatchC05120PlusMidpointBounds2559

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC05120PlusThirdCell2559 (i : Fin 30) : ℝ :=
  max (batchC05120PlusLeftNormUpper2559 i) (batchC05120PlusRightNormUpper2559 i) +
    batchC05120PlusFourthUpper2559 i * ((batchN05121PlusPosition2559 -
        batchN05120PlusPosition2559) / 2)

theorem batchC05120PlusThirdCell_bound2559 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN05120PlusPosition2559 batchN05121PlusPosition2559 ≤ batchC05120PlusThirdCell2559 i :=
          by
  have hh : 0 ≤ (batchN05121PlusPosition2559 - batchN05120PlusPosition2559) / 2 := by
    norm_num [batchN05121PlusPosition2559, batchN05120PlusPosition2559]
  have hf := batchC05120PlusFourthBound2559 i
  unfold weightedFamilyThirdCellUpper2538 batchC05120PlusThirdCell2559
  by_cases hi : cellNearAbs2538 batchN05120PlusPosition2559 batchN05121PlusPosition2559 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC05120PlusFourthCell2559 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC05120PlusLeftNormBound2559 i
    · simpa only [weightedUnitJet2539] using batchC05120PlusRightNormBound2559 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC05120PlusLeftNormUpper2559 i := (norm_nonneg _).trans
        (batchC05120PlusLeftNormBound2559 i)
    unfold batchC05120PlusFourthCell2559 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC05120PlusThirdAggregate2559 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC05120PlusThirdCell2559 i

theorem batchC05120PlusThirdAggregate_bound2559 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05120PlusPosition2559 batchN05121PlusPosition2559 ≤
          batchC05120PlusThirdAggregate2559 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC05120PlusThirdCell_bound2559 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC05120PlusCurvature_bound2559 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN05120PlusPosition2559 batchN05121PlusPosition2559 ≤
        batchC05120PlusSignedMidpointUpper2559 + batchC05120PlusThirdAggregate2559 *
          ((batchN05121PlusPosition2559 - batchN05120PlusPosition2559) / 2) := by
  have hm : (batchN05120PlusPosition2559 + batchN05121PlusPosition2559) / 2 =
      batchC05120PlusMidpointPosition2559 := by
    norm_num [batchN05120PlusPosition2559, batchN05121PlusPosition2559,
        batchC05120PlusMidpointPosition2559]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC05120PlusSignedMidpointUpper_le2559
  apply mul_le_mul_of_nonneg_right batchC05120PlusThirdAggregate_bound2559
  norm_num [batchN05121PlusPosition2559, batchN05120PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120PlusThirdCell_bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusThirdAggregate_bound2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusCurvature_bound2559
