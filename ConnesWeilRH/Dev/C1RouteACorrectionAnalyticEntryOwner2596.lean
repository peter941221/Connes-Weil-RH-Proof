import ConnesWeilRH.Dev.C1RouteACorrectionDefectEntryBounds2595
import ConnesWeilRH.Dev.C1RouteACorrectionEntrywiseDefect2592

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-! The 2595 Fraction payload is now connected to the existing entrywise
Neumann interface. The analytic entry enclosure and defect-matrix identity are
still explicit premises. -/

theorem capturedActualCorrectionOwner2584_realizes_of_analytic_entry_bounds2596
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (hentry : ∀ i j : Fin 30,
      ‖defectMatrix i j‖₊ ≤ analyticDefectEntryBounds2595 i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_entrywise_defect_bounds2592
    X defectMatrix analyticDefectEntryBounds2595 hentry
  · intro i
    rw [analyticDefectEntryBounds2595_row_sum i]
    exact analyticDefectRowBounds2593_lt_one i
  · exact hdefect_matrix

end ConnesWeilRH.Dev

