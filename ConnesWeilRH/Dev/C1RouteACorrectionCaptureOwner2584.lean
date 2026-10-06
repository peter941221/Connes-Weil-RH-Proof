import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteACorrectionMembershipBridge2583

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

noncomputable def capturedActualCorrectionOwner2584 : Fin 30 → ℂ :=
  actualCorrectionOwner2351 capturedModulations2584 capturedNodes2584 capturedTargets2584

theorem capturedActualCorrectionOwner2584_realizes
    (hdet : IsUnit
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584).det)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  exact actualCorrectionOwner2351_realizes capturedModulations2584
    capturedNodes2584 capturedTargets2584 hdet row

theorem capturedActualCorrectionOwner2584_mem_of_component_distances
    (hcomponent : ∀ i : Fin 30,
      |(capturedActualCorrectionOwner2584 i).re -
          (correctionCoefficientCenter2570 i).re| ≤
        ((correctionCoefficientBox2570 i).reHi -
          (correctionCoefficientBox2570 i).reLo) / 2 ∧
      |(capturedActualCorrectionOwner2584 i).im -
          (correctionCoefficientCenter2570 i).im| ≤
        ((correctionCoefficientBox2570 i).imHi -
          (correctionCoefficientBox2570 i).imLo) / 2) :
    ∀ i : Fin 30,
      (correctionCoefficientBox2570 i).Mem
        (capturedActualCorrectionOwner2584 i) := by
  exact actualCorrectionOwner2351_mem_of_component_distances2583
    capturedModulations2584 capturedNodes2584 capturedTargets2584 hcomponent

end ConnesWeilRH.Dev
