import ConnesWeilRH.Dev.C1RouteACorrectionDefectRows2591

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-- Entrywise nonnegative bounds are enough; the complex defect entries remain
separate analytic objects and are never replaced by their bounds. -/
theorem capturedActualCorrectionOwner2584_realizes_of_entrywise_defect_bounds2592
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (bounds : Matrix (Fin 30) (Fin 30) NNReal)
    (hentry : ∀ i j : Fin 30, ‖defectMatrix i j‖₊ ≤ bounds i j)
    (hrows : ∀ i : Fin 30, ∑ j : Fin 30, bounds i j < 1)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_defect2589 X
  rw [hdefect_matrix]
  exact matrixOperator_norm_lt_one_of_entrywise_bounds2590
    defectMatrix bounds hentry hrows

end ConnesWeilRH.Dev