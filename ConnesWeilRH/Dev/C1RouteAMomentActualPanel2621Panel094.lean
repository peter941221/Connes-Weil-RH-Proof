import ConnesWeilRH.Dev.C1RouteAMomentPanelTable2621Panel094

namespace ConnesWeilRH.Dev

open Set
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem momentPanelDenominator_eval2621 (position : ℝ) :
    polynomialEval2621 momentPanelDenominator2621 position =
      (1 - ((9 / 200 : ℝ) + position) ^ 2) ^ 2 := by
  rw [momentPanelDenominator2621, polynomialEval_mul2621]
  norm_num [momentPanelDeficit2621, polynomialEval2621]
  ring

theorem momentPanelNumerator_eval2621 (position : ℝ) :
    polynomialEval2621 momentPanelNumerator2621 position =
      (momentBeta2620 : ℝ) * (1 - ((9 / 200 : ℝ) + position) ^ 2) ^ 2 -
        60 * ((9 / 200 : ℝ) + position) := by
  rw [momentPanelNumerator2621, polynomialEval_add2621, polynomialEval_scale2621,
    polynomialEval_scale2621, momentPanelDenominator_eval2621]
  norm_num [polynomialEval2621]
  ring

theorem momentPanelResidual_eval2621 (position : ℝ) :
    polynomialEval2621 momentPanelResidual2621 position =
      momentPolynomialResidual2619 (momentBeta2620 : ℝ) (9 / 200)
        (polynomialEval2621 momentPanelPolynomial2621)
        (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2621)) position := by
  rw [← momentPanelResidual_replay2621, polynomialEval_add2621, polynomialEval_mul2621,
    polynomialEval_scale2621, polynomialEval_mul2621, momentPanelDenominator_eval2621,
    momentPanelNumerator_eval2621]
  simp only [momentPolynomialResidual2619, Rat.cast_neg, Rat.cast_one]
  ring

theorem momentPanelResidual_bound2621 (position : ℝ)
    (hposition : position ∈ Icc (-(1 / 200 : ℝ)) (1 / 200)) :
    |momentPolynomialResidual2619 (momentBeta2620 : ℝ) (9 / 200)
      (polynomialEval2621 momentPanelPolynomial2621)
      (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2621)) position| ≤
      (momentPanelResidualUpper2621 : ℝ) := by
  rw [← momentPanelResidual_eval2621, ← momentPanelResidualUpper_replay2621]
  apply polynomialEval_abs_le2621 _ (1 / 200) (by norm_num)
  simpa using abs_le.mpr hposition

theorem momentPanelPolynomial_integral2621 :
    (∫ position in (-(1 / 200 : ℝ))..(1 / 200),
      polynomialEval2621 momentPanelPolynomial2621 position) = (momentPanelIntegral2621 : ℝ) := by
  have h := polynomialEval_integral2621 momentPanelPolynomial2621 momentPanelPrimitive2621
    momentPanelPrimitive_replay2621 (-1 / 200) (1 / 200)
  rw [momentPanelIntegral_replay2621] at h
  convert h using 1
  norm_num

theorem momentPanelPhase_error2621 :
    |(∫ position in (-(1 / 200 : ℝ))..(1 / 200),
        Real.exp (momentPhase2619 (momentBeta2620 : ℝ) (9 / 200) position)) -
      Real.exp (momentPhase2619 (momentBeta2620 : ℝ) (9 / 200) 0) *
        (momentPanelIntegral2621 : ℝ)| ≤ (momentPanelAnalyticCharge2621 : ℝ) := by
  have hbase := momentPhase_integral_error_of_polynomialResidual2619
    (momentBeta2620 : ℝ) (9 / 200) (polynomialEval2621 momentPanelPolynomial2621)
    (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2621)) (1 / 200)
    (momentPanelResidualUpper2621 : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg2621)
    (by norm_num [momentPanelPolynomial2621, polynomialEval2621])
    (fun position _ => polynomialEval_hasDerivAt2621 _ position)
    momentPanelResidual_bound2621
  rw [momentPanelPolynomial_integral2621] at hbase
  have hamplitude := (abs_le.mp momentScalarAmplitude2620_error).2
  have hgrowth := (abs_le.mp momentScalarGrowth2620_error).2
  rw [← momentBeta_owner2620] at hamplitude hgrowth
  have hamplitudeUpper : Real.exp
      (momentPhase2619 (momentBeta2620 : ℝ) (9 / 200) 0) ≤
      (momentScalarAmplitude2620Expected.1.1 : ℝ) + (momentScalarAmplitude2620Expected.2 : ℝ) := by
    linarith
  have hgrowthUpper : Real.exp (2 * momentPhaseSlopeUpper2619 (momentBeta2620 : ℝ)
      (9 / 200) (1 / 200) * (1 / 200)) ≤
      (momentScalarGrowth2620Expected.1.1 : ℝ) + (momentScalarGrowth2620Expected.2 : ℝ) := by
    linarith
  have hproduct := mul_le_mul hamplitudeUpper hgrowthUpper
    (le_of_lt (Real.exp_pos _))
    ((le_of_lt (Real.exp_pos _)).trans hamplitudeUpper)
  apply hbase.trans
  have hfactor : 0 ≤ (momentPanelResidualUpper2621 : ℝ) /
      (1 - (|(9 / 200 : ℝ)| + 1 / 200) ^ 2) ^ 2 :=
    div_nonneg (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg2621) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hproduct hfactor)
    (by positivity : 0 ≤ (2 : ℝ) * (1 / 200) ^ 2)
  simpa only [momentPanelAnalyticCharge2621, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using h

theorem actualMomentPanel094_integral_certificate2621 :
    |(storedWidth 0 ^ 2) *
      (∫ position in (-(1 / 200 : ℝ))..(1 / 200),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
          ((9 / 200 : ℝ) + position)) - (momentPanelIntegralCenter2621 : ℝ)| ≤
      (momentPanelIntegralCharge2621 : ℝ) := by
  have hphase : (∫ position in (-(1 / 200 : ℝ))..(1 / 200),
      realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
        ((9 / 200 : ℝ) + position)) =
      (∫ position in (-(1 / 200 : ℝ))..(1 / 200),
        Real.exp (momentPhase2619 (momentBeta2620 : ℝ) (9 / 200) position)) := by
    apply intervalIntegral.integral_congr
    intro position hposition
    rw [Set.uIcc_of_le (by norm_num : -(1 / 200 : ℝ) ≤ 1 / 200)] at hposition
    rw [momentBeta_owner2620]
    exact realNormalizedMomentIntegrand2618_eq_phase2619 _ _ _ _
      (momentPanel_interior2619 (9 / 200) (1 / 200) position (by norm_num) hposition)
  rw [hphase, ← momentRadius_owner2620]
  have hcenter : (momentRadius2620 : ℝ) * (momentScalarAmplitude2620Expected.1.1 : ℝ) *
      (momentPanelIntegral2621 : ℝ) = (momentPanelIntegralCenter2621 : ℝ) := by
    exact_mod_cast momentPanelCenter_replay2621
  have hcharge : (momentRadius2620 : ℝ) * ((momentPanelAnalyticCharge2621 : ℝ) +
      (momentScalarAmplitude2620Expected.2 : ℝ) * |(momentPanelIntegral2621 : ℝ)|) =
      (momentPanelIntegralCharge2621 : ℝ) := by
    exact_mod_cast momentPanelCharge_replay2621
  have hamplitude := momentScalarAmplitude2620_error
  rw [← momentBeta_owner2620] at hamplitude
  have hradius : 0 < (momentRadius2620 : ℝ) := by
    rw [momentRadius_owner2620]
    exact pow_pos (storedWidth_pos 0) 2
  rw [← hcenter, mul_assoc, ← mul_sub, abs_mul, abs_of_pos hradius]
  apply (mul_le_mul_of_nonneg_left
    ((abs_sub_le _ _ _).trans (add_le_add momentPanelPhase_error2621
      (show |Real.exp (momentPhase2619 (momentBeta2620 : ℝ) (9 / 200) 0) *
          (momentPanelIntegral2621 : ℝ) - (momentScalarAmplitude2620Expected.1.1 : ℝ) *
            (momentPanelIntegral2621 : ℝ)| ≤
          (momentScalarAmplitude2620Expected.2 : ℝ) * |(momentPanelIntegral2621 : ℝ)| from by
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right hamplitude (abs_nonneg _)))) hradius.le).trans_eq hcharge

theorem actualMomentPanel094_integral_error_le2621 :
    |(storedWidth 0 ^ 2) *
      (∫ position in (1 / 25 : ℝ)..(1 / 20),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re position) -
      (momentPanelIntegralCenter2621 : ℝ)| ≤ (1 : ℝ) / 10 ^ 82 := by
  have h := actualMomentPanel094_integral_certificate2621
  rw [intervalIntegral.integral_comp_add_left] at h
  norm_num only at h
  have hupper : (momentPanelIntegralCharge2621 : ℝ) ≤ ((1 / 10 ^ 82 : ℚ) : ℝ) :=
    Rat.cast_le.mpr momentPanelCharge_le2621
  exact h.trans (by simpa using hupper)

end ConnesWeilRH.Dev
