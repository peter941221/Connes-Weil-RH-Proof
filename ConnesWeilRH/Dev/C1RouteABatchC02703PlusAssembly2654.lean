import ConnesWeilRH.Dev.C1RouteABatchC02703PlusFourth2654
import ConnesWeilRH.Dev.C1RouteABatchC02703PlusLeftBounds2654
import ConnesWeilRH.Dev.C1RouteABatchC02703PlusRightBounds2654
import ConnesWeilRH.Dev.C1RouteABatchC02703PlusMidpointBounds2654

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02703PlusThirdCell2654 (i : Fin 30) : ℝ :=
  max (batchC02703PlusLeftNormUpper2654 i) (batchC02703PlusRightNormUpper2654 i) +
    batchC02703PlusFourthUpper2654 i * ((batchN02704PlusPosition2654 -
        batchN02703PlusPosition2654) / 2)

theorem batchC02703PlusThirdCell_bound2654 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      batchN02703PlusPosition2654 batchN02704PlusPosition2654 ≤ batchC02703PlusThirdCell2654 i :=
          by
  have hh : 0 ≤ (batchN02704PlusPosition2654 - batchN02703PlusPosition2654) / 2 := by
    norm_num [batchN02704PlusPosition2654, batchN02703PlusPosition2654]
  have hf := batchC02703PlusFourthBound2654 i
  unfold weightedFamilyThirdCellUpper2538 batchC02703PlusThirdCell2654
  by_cases hi : cellNearAbs2538 batchN02703PlusPosition2654 batchN02704PlusPosition2654 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC02703PlusFourthCell2654 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC02703PlusLeftNormBound2654 i
    · simpa only [weightedUnitJet2539] using batchC02703PlusRightNormBound2654 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC02703PlusLeftNormUpper2654 i := (norm_nonneg _).trans
        (batchC02703PlusLeftNormBound2654 i)
    unfold batchC02703PlusFourthCell2654 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC02703PlusThirdAggregate2654 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02703PlusThirdCell2654 i

theorem batchC02703PlusThirdAggregate_bound2654 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02703PlusPosition2654 batchN02704PlusPosition2654 ≤
          batchC02703PlusThirdAggregate2654 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02703PlusThirdCell_bound2654 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC02703PlusCurvature_bound2654 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchN02703PlusPosition2654 batchN02704PlusPosition2654 ≤
        batchC02703PlusSignedMidpointUpper2654 + batchC02703PlusThirdAggregate2654 *
          ((batchN02704PlusPosition2654 - batchN02703PlusPosition2654) / 2) := by
  have hm : (batchN02703PlusPosition2654 + batchN02704PlusPosition2654) / 2 =
      batchC02703PlusMidpointPosition2654 := by
    norm_num [batchN02703PlusPosition2654, batchN02704PlusPosition2654,
        batchC02703PlusMidpointPosition2654]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC02703PlusSignedMidpointUpper_le2654
  apply mul_le_mul_of_nonneg_right batchC02703PlusThirdAggregate_bound2654
  norm_num [batchN02704PlusPosition2654, batchN02703PlusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusThirdCell_bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusThirdAggregate_bound2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusCurvature_bound2654
