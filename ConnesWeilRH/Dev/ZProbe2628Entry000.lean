import ConnesWeilRH.Dev.ZProbe2628RealError
import ConnesWeilRH.Dev.C1RouteAAnalyticMomentDiagonal2618

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

 theorem actualOwnerMomentMatrix2351_entry000_mem2628 :
    (analyticMomentInterval2597 0 0).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 0) := by
  have hphase := capturedDiagonalPhase2618 0
  have hentry := momentEntry2351_eq_realIntegral_of_phase_cancel2618
    capturedModulations2584 0 (capturedNodes2584 0) hphase
  have him := actualOwnerMomentMatrix2351_diagonal_im_eq_zero2618 0
  have herr := actualFullRealError2628
  have herrlo := (abs_le.mp herr).1
  have herrhi := (abs_le.mp herr).2
  have hmarginLo :
      (analyticMomentInterval2597 0 0).reLo +
          ((2 : ℚ) / 10 ^ 68 +
            ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) ≤
        ((totalCenters2628 : ℚ) : ℝ) := by
    rw [totalCenters_replay2628]
    norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_00,
      dec2628, Finset.sum_range_succ]
  have hmarginHi :
      ((totalCenters2628 : ℚ) : ℝ) +
          ((2 : ℚ) / 10 ^ 68 +
            ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) ≤
        (analyticMomentInterval2597 0 0).reHi := by
    rw [totalCenters_replay2628]
    norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_00,
      dec2628, Finset.sum_range_succ]
  change (analyticMomentInterval2597 0 0).Mem
    (momentEntry2351 capturedModulations2584 0 (capturedNodes2584 0))
  rw [hentry]
  change (analyticMomentInterval2597 0 0).reLo ≤
      storedWidth 0 ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
          (capturedNodes2584 0).re coordinate) ∧
    storedWidth 0 ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
          (capturedNodes2584 0).re coordinate) ≤
      (analyticMomentInterval2597 0 0).reHi ∧
    (analyticMomentInterval2597 0 0).imLo ≤ 0 ∧
    0 ≤ (analyticMomentInterval2597 0 0).imHi
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · have himem := actualOwnerMomentMatrix2351_entry000_im_mem2618
    rw [him] at himem
    exact himem.1
  · have himem := actualOwnerMomentMatrix2351_entry000_im_mem2618
    rw [him] at himem
    exact himem.2

end ConnesWeilRH.Dev
