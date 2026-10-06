import ConnesWeilRH.Dev.C1RouteACorrectionRowBounds2593
import ConnesWeilRH.Dev.C1RouteACorrectionDefectOwner2589

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-- The exported 2351 row-bound payload is enough once its containment in the
actual defect matrix has been proved. -/
theorem capturedActualCorrectionOwner2584_realizes_of_row_bounds2594
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (hrows : ∀ i : Fin 30,
      (∑ j : Fin 30, ‖defectMatrix i j‖₊) ≤ analyticDefectRowBounds2593 i)
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
  apply matrixOperator_norm_lt_one_of_row_norm_bounds2590
    defectMatrix analyticDefectRowBounds2593 hrows
  exact analyticDefectRowBounds2593_lt_one

end ConnesWeilRH.Dev