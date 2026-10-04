import ConnesWeilRH.Dev.C1RouteABatchC02702PlusFourth2558
import ConnesWeilRH.Dev.C1RouteABatchC02702PlusLeftBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02702PlusRightBounds2558
import ConnesWeilRH.Dev.C1RouteABatchC02702PlusMidpointBounds2558

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def batchC02702PlusThirdCell2558 (i : Fin 30) : ℝ :=
  max (batchC02702PlusLeftNormUpper2558 i) (batchC02702PlusRightNormUpper2558 i) +
    batchC02702PlusFourthUpper2558 i * ((batchN02703PlusPosition2558 - neighborRightPosition2557)
        / 2)

theorem batchC02702PlusThirdCell_bound2558 (i : Fin 30) :
    weightedFamilyThirdCellUpper2538 (1/2) 1 (nodeModulation2541 i) (storedWidth i ^ 2)
      neighborRightPosition2557 batchN02703PlusPosition2558 ≤ batchC02702PlusThirdCell2558 i := by
  have hh : 0 ≤ (batchN02703PlusPosition2558 - neighborRightPosition2557) / 2 := by
    norm_num [batchN02703PlusPosition2558, neighborRightPosition2557]
  have hf := batchC02702PlusFourthBound2558 i
  unfold weightedFamilyThirdCellUpper2538 batchC02702PlusThirdCell2558
  by_cases hi : cellNearAbs2538 neighborRightPosition2557 batchN02703PlusPosition2558 <
      storedWidth i ^ 2
  · rw [if_pos hi]
    unfold batchC02702PlusFourthCell2558 at hf
    rw [if_pos hi] at hf
    apply add_le_add (max_le_max ?_ ?_) (mul_le_mul_of_nonneg_right hf hh)
    · simpa only [weightedUnitJet2539] using batchC02702PlusLeftNormBound2558 i
    · simpa only [weightedUnitJet2539] using batchC02702PlusRightNormBound2558 i
  · rw [if_neg hi]
    have hl : 0 ≤ batchC02702PlusLeftNormUpper2558 i := (norm_nonneg _).trans
        (batchC02702PlusLeftNormBound2558 i)
    unfold batchC02702PlusFourthCell2558 at hf
    rw [if_neg hi] at hf
    exact add_nonneg (hl.trans (le_max_left _ _)) (mul_nonneg hf hh)

noncomputable def batchC02702PlusThirdAggregate2558 : ℝ :=
  ∑ i : Fin 30, (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *
      batchC02702PlusThirdCell2558 i

theorem batchC02702PlusThirdAggregate_bound2558 :
    signedThirdCellUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 neighborRightPosition2557 batchN02703PlusPosition2558 ≤
          batchC02702PlusThirdAggregate2558 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (batchC02702PlusThirdCell_bound2558 i)
    (add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540]))

theorem batchC02702PlusCurvature_bound2558 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 neighborRightPosition2557 batchN02703PlusPosition2558 ≤
        batchC02702PlusSignedMidpointUpper2558 + batchC02702PlusThirdAggregate2558 *
          ((batchN02703PlusPosition2558 - neighborRightPosition2557) / 2) := by
  have hm : (neighborRightPosition2557 + batchN02703PlusPosition2558) / 2 =
      batchC02702PlusMidpointPosition2558 := by
    norm_num [neighborRightPosition2557, batchN02703PlusPosition2558,
        batchC02702PlusMidpointPosition2558]
  unfold signedCurvatureUpper2539
  rw [hm]
  apply add_le_add batchC02702PlusSignedMidpointUpper_le2558
  apply mul_le_mul_of_nonneg_right batchC02702PlusThirdAggregate_bound2558
  norm_num [batchN02703PlusPosition2558, neighborRightPosition2557]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusThirdCell_bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusThirdAggregate_bound2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusCurvature_bound2558
