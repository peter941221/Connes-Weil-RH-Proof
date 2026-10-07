import ConnesWeilRH.Dev.C1RouteAAnalyticMomentNormalization2618
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticIntervals2597

namespace ConnesWeilRH.Dev

theorem capturedDiagonalPhase2618 (index : Fin 30) :
    (capturedNodes2584 index).im + capturedModulations2584 index = 0 := by
  fin_cases index <;> norm_num [capturedNodes2584, capturedModulations2584]

theorem actualOwnerMomentMatrix2351_diagonal_im_eq_zero2618 (index : Fin 30) :
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 index index).im = 0 := by
  exact momentEntry2351_im_eq_zero_of_phase_cancel2618 _ _ _ (capturedDiagonalPhase2618 index)

theorem actualOwnerMomentMatrix2351_entry000_im_mem2618 :
    (analyticMomentInterval2597 0 0).imLo ≤
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 0).im ∧
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 0).im ≤
        (analyticMomentInterval2597 0 0).imHi := by
  rw [actualOwnerMomentMatrix2351_diagonal_im_eq_zero2618]
  norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_00]

end ConnesWeilRH.Dev
