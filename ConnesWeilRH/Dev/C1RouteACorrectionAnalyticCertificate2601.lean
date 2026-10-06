import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600
import ConnesWeilRH.Dev.C1RouteACorrectionIntervalOwner2599

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-! Integrated certificate interface. The remaining premises are exactly the
candidate-inverse containment, analytic integral interval soundness, and the
operator realization of the actual defect. -/

theorem capturedActualCorrectionOwner2584_realizes_of_analytic_interval_certificate2601
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (defectMatrix : Matrix (Fin 30) (Fin 30) ℂ)
    (x : Matrix (Fin 30) (Fin 30) ℂ)
    (hx : ∀ i k : Fin 30,
      (candidateInverseInterval2600 i k).Mem (x i k))
    (hinterval : ∀ k j : Fin 30,
      (analyticMomentInterval2597 k j).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 k j))
    (hdefect_entry : ∀ i j : Fin 30,
      defectMatrix i j = matrixDefectEntry2598 x
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584) i j)
    (hdefect_matrix :
      (ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
          X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) =
        matrixOperator2590 defectMatrix)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes_of_interval_defect_bounds2599
    X defectMatrix x (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584)
    candidateInverseInterval2600 analyticMomentInterval2597 hx hinterval
    hdefect_entry
  · exact candidateInverseDefectEntryBound2600
  · exact hdefect_matrix

end ConnesWeilRH.Dev
