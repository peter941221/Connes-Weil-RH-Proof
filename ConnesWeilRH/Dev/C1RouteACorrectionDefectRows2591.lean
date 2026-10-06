import ConnesWeilRH.Dev.C1RouteACorrectionDefectOwner2589
import ConnesWeilRH.Dev.C1RouteACorrectionOperatorNorm2590

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-- A finite row-sum certificate for the defect matrix supplies the operator
norm premise required by the captured-owner interpolation theorem. -/
theorem capturedActualCorrectionOwner2584_realizes_of_defect_rows2591
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (hrows : ∀ i : Fin 30, ∑ j : Fin 30, ‖defectMatrix i j‖ < 1)
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
  exact matrixOperator_norm_lt_one_of_row_sum_lt_one2590 defectMatrix hrows

end ConnesWeilRH.Dev