import ConnesWeilRH.Dev.C1RouteACorrectionCaptureOwner2584
import ConnesWeilRH.Dev.C1RouteACorrectionMomentOperator2588

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

/-- The captured owner interpolation theorem with the Neumann defect as its
only invertibility premise. The defect itself remains an external certificate
until the 2338 analytic matrix bounds are imported. -/
theorem capturedActualCorrectionOwner2584_realizes_of_defect2589
    (X : (Fin 30 → ℂ) →L[ℂ] (Fin 30 → ℂ))
    (hdefect :
      ‖(ContinuousLinearMap.id ℂ (Fin 30 → ℂ)) -
        X.comp (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584)‖ < 1)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      capturedActualCorrectionOwner2584 capturedModulations2584)
      (capturedNodes2584 row) = capturedTargets2584 row := by
  apply capturedActualCorrectionOwner2584_realizes
  apply isUnit_iff_ne_zero.mpr
  apply ownerMomentMatrix_det_ne_zero_of_operator_injective2588
  exact injective_of_norm_sub_id_lt_one2587_left_factor
    (ownerMomentOperator2588 capturedModulations2584 capturedNodes2584) X hdefect

end ConnesWeilRH.Dev