import ConnesWeilRH.Dev.C1RouteARationalSignedFamily3332

namespace ConnesWeilRH.Dev

def ratRectRealEndpointAbsBound3342 (a : RatRect3276) : ℚ :=
  max |a.reLo| |a.reHi|

def ratRectImagEndpointAbsBound3342 (a : RatRect3276) : ℚ :=
  max |a.imLo| |a.imHi|

theorem ratRect_reLo_ge_neg_abs_bound3342 (a : RatRect3276) :
    -ratRectRealEndpointAbsBound3342 a ≤ a.reLo := by
  unfold ratRectRealEndpointAbsBound3342
  exact le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _)

theorem ratRect_imHi_le_abs_bound3342 (a : RatRect3276) :
    a.imHi ≤ ratRectImagEndpointAbsBound3342 a := by
  unfold ratRectImagEndpointAbsBound3342
  exact le_trans (le_abs_self _) (le_max_right _ _)

theorem signed_singleton_reHi_le_coordinate_bound3342
    (cRe cIm : ℚ) (b : RatRect3276)
    (hcRe : cRe ≤ 0) (hcIm : cIm ≤ 0) :
    (RatRect3276.mul
      ({ reLo := cRe, reHi := cRe, imLo := cIm, imHi := cIm } : RatRect3276)
      b).reHi ≤
      (-cRe) * ratRectRealEndpointAbsBound3342 b +
        (-cIm) * ratRectImagEndpointAbsBound3342 b := by
  rw [ratRect_mul_singleton_reHi_formula3331]
  have hre :
      cRe * b.reLo ≤ (-cRe) * ratRectRealEndpointAbsBound3342 b := by
    have hneg : -ratRectRealEndpointAbsBound3342 b ≤ b.reLo :=
      ratRect_reLo_ge_neg_abs_bound3342 b
    have hnonneg : 0 ≤ -cRe := neg_nonneg.mpr hcRe
    have hmul := mul_le_mul_of_nonneg_left hneg hnonneg
    linarith
  have him :
      -(cIm * b.imHi) ≤ (-cIm) * ratRectImagEndpointAbsBound3342 b := by
    have himHi := ratRect_imHi_le_abs_bound3342 b
    have hnonneg : 0 ≤ -cIm := neg_nonneg.mpr hcIm
    have hmul := mul_le_mul_of_nonneg_left himHi hnonneg
    nlinarith
  have himLo :
      -(cIm * b.imLo) ≤ (-cIm) * ratRectImagEndpointAbsBound3342 b := by
    have himLo' :
        b.imLo ≤ ratRectImagEndpointAbsBound3342 b := by
      unfold ratRectImagEndpointAbsBound3342
      exact le_trans (le_abs_self _) (le_max_left _ _)
    have hnonneg : 0 ≤ -cIm := neg_nonneg.mpr hcIm
    have hmul := mul_le_mul_of_nonneg_left himLo' hnonneg
    nlinarith
  have hmax :
      max (cRe * b.reLo) (cRe * b.reHi) ≤
        (-cRe) * ratRectRealEndpointAbsBound3342 b := by
    apply max_le hre
    have hhi : -ratRectRealEndpointAbsBound3342 b ≤ b.reHi := by
      exact le_trans (neg_le_neg (le_max_right _ _)) (neg_abs_le _)
    have hnonneg : 0 ≤ -cRe := neg_nonneg.mpr hcRe
    have hmul := mul_le_mul_of_nonneg_left hhi hnonneg
    linarith
  have hmin :
      -(min (cIm * b.imLo) (cIm * b.imHi)) ≤
        (-cIm) * ratRectImagEndpointAbsBound3342 b := by
    by_cases h : cIm * b.imLo ≤ cIm * b.imHi
    · rw [min_eq_left h]
      exact himLo
    · rw [min_eq_right (le_of_not_ge h)]
      exact him
  linarith

theorem signed_selected_reHi_le_coordinate_bound3342
    (cRe cIm : ℚ) (b : RatRect3276)
    (hcRe : cRe ≤ 0) (hcIm : cIm ≤ 0) :
    cRe * b.reLo - cIm * b.imHi ≤
      (-cRe) * ratRectRealEndpointAbsBound3342 b +
        (-cIm) * ratRectImagEndpointAbsBound3342 b := by
  have hreal :
      cRe * b.reLo ≤ (-cRe) * ratRectRealEndpointAbsBound3342 b := by
    have hneg := ratRect_reLo_ge_neg_abs_bound3342 b
    have hnonneg : 0 ≤ -cRe := neg_nonneg.mpr hcRe
    have hmul := mul_le_mul_of_nonneg_left hneg hnonneg
    linarith
  have himag :
      -(cIm * b.imHi) ≤ (-cIm) * ratRectImagEndpointAbsBound3342 b := by
    have himHi := ratRect_imHi_le_abs_bound3342 b
    have hnonneg : 0 ≤ -cIm := neg_nonneg.mpr hcIm
    have hmul := mul_le_mul_of_nonneg_left himHi hnonneg
    nlinarith
  linarith

theorem ratWeightedPhysicalTermRect3310_family4_reHi_le_coordinate_bound3342
    (cell : ℕ)
    (hre : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reHi)
    (him : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi) :
    (ratWeightedPhysicalTermRect3310 2 cell 4).reHi ≤
      (-((ratCoefficientRect3282 4).reHi)) *
          ratRectRealEndpointAbsBound3342
            (RatRect3276.add
              (RatRect3276.add
                (ratWeightedUnitJetRect3310 2 0 cell 4)
                (ratWeightedUnitJetRect3310 2 1 cell 4))
              (ratWeightedUnitJetRect3310 2 2 cell 4)) +
      (-((ratCoefficientRect3282 4).imHi)) *
          ratRectImagEndpointAbsBound3342
            (RatRect3276.add
              (RatRect3276.add
                (ratWeightedUnitJetRect3310 2 0 cell 4)
                (ratWeightedUnitJetRect3310 2 1 cell 4))
              (ratWeightedUnitJetRect3310 2 2 cell 4)) := by
  rw [ratWeightedPhysicalTermRect3310_family4_reHi_signed3332
    cell hre him]
  apply signed_selected_reHi_le_coordinate_bound3342
  · exact (ratCoefficientRect3282_family4_signs3332.1).le
  · exact (ratCoefficientRect3282_family4_signs3332.2).le

end ConnesWeilRH.Dev
