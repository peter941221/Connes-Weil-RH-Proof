import ConnesWeilRH.Dev.C1RouteACorrectionIntervalPropagation2598
import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticEntryOwner2596

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-! Conditional end-to-end interface from interval propagation to owner
realization. The analytic interval, candidate-inverse interval, and finite
rational comparison remain explicit premises. -/

theorem capturedActualCorrectionOwner2584_realizes_of_interval_defect_bounds2599
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (x a : Matrix (Fin 30) (Fin 30) ℂ)
    (xRect aRect : Matrix (Fin 30) (Fin 30) ComplexRect2427)
    (hx : ∀ i k : Fin 30, (xRect i k).Mem (x i k))
    (ha : ∀ k j : Fin 30, (aRect k j).Mem (a k j))
    (hdefect_entry : ∀ i j : Fin 30,
      defectMatrix i j = matrixDefectEntry2598 x a i j)
    (hbound : ∀ i j : Fin 30,
      rectL1Upper2598 (matrixDefectInterval2598 xRect aRect i j) ≤
        analyticDefectEntryBounds2595 i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_analytic_entry_bounds2596
    X defectMatrix
  · intro i j
    rw [hdefect_entry i j]
    exact (norm_le_rectL1Upper2598 (matrixDefectInterval2598_mem
      x a xRect aRect hx ha i j)).trans (hbound i j)
  · exact hdefect_matrix

end ConnesWeilRH.Dev
