import ConnesWeilRH.Dev.C1RouteAMomentPanelTable2622K03Panel164

namespace ConnesWeilRH.Dev

open Set
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem momentPanelDenominator_eval2622K03P164 (position : ℝ) :
    polynomialEval2621 momentPanelDenominator2622K03P164 position =
      (1 - ((149 / 200) + position) ^ 2) ^ 2 := by
  rw [momentPanelDenominator2622K03P164, polynomialEval_mul2621]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelDeficit2622K03P164, polynomialEval2621]
  ring

theorem momentPanelNumerator_eval2622K03P164 (position : ℝ) :
    polynomialEval2621 momentPanelNumerator2622K03P164 position =
      (momentBeta2620K03 : ℝ) * (1 - ((149 / 200) + position) ^ 2) ^ 2 -
        60 * ((149 / 200) + position) := by
  rw [momentPanelNumerator2622K03P164, polynomialEval_add2621, polynomialEval_scale2621,
    polynomialEval_scale2621, momentPanelDenominator_eval2622K03P164]
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, polynomialEval2621]
  ring

theorem momentPanelResidual_eval2622K03P164 (position : ℝ) :
    polynomialEval2621 momentPanelResidual2622K03P164 position =
      momentPolynomialResidual2619 (momentBeta2620K03 : ℝ) (149 / 200)
        (polynomialEval2621 momentPanelPolynomial2622K03P164)
        (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2622K03P164)) position := by
  rw [← momentPanelResidual_replay2622K03P164, polynomialEval_add2621, polynomialEval_mul2621,
    polynomialEval_scale2621, polynomialEval_mul2621, momentPanelDenominator_eval2622K03P164,
    momentPanelNumerator_eval2622K03P164]
  simp only [momentPolynomialResidual2619, Rat.cast_neg, Rat.cast_one]
  ring

theorem momentPanelResidual_bound2622K03P164 (position : ℝ)
    (hposition : position ∈ Icc (-(1 / 200)) (1 / 200)) :
    |momentPolynomialResidual2619 (momentBeta2620K03 : ℝ) (149 / 200)
      (polynomialEval2621 momentPanelPolynomial2622K03P164)
      (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2622K03P164)) position| ≤
      (momentPanelResidualUpper2622K03P164 : ℝ) := by
  rw [← momentPanelResidual_eval2622K03P164, ← momentPanelResidualUpper_replay2622K03P164]
  apply polynomialEval_abs_le2621 _ (1 / 200) (by norm_num)
  simpa using abs_le.mpr hposition

theorem momentPanelPolynomial_integral2622K03P164 :
    (∫ position in (-(1 / 200))..(1 / 200),
      polynomialEval2621 momentPanelPolynomial2622K03P164 position) = (momentPanelIntegral2622K03P164 : ℝ) := by
  have h := polynomialEval_integral2621 momentPanelPolynomial2622K03P164 momentPanelPrimitive2622K03P164
    momentPanelPrimitive_replay2622K03P164 (-1 / 200) (1 / 200)
  rw [momentPanelIntegral_replay2622K03P164] at h
  convert h using 1
  norm_num

theorem momentPanelPhase_error2622K03P164 :
    |(∫ position in (-(1 / 200))..(1 / 200),
        Real.exp (momentPhase2619 (momentBeta2620K03 : ℝ) (149 / 200) position)) -
      Real.exp (momentPhase2619 (momentBeta2620K03 : ℝ) (149 / 200) 0) *
        (momentPanelIntegral2622K03P164 : ℝ)| ≤ (momentPanelAnalyticCharge2622K03P164 : ℝ) := by
  have hbase := momentPhase_integral_error_of_polynomialResidual2619
    (momentBeta2620K03 : ℝ) (149 / 200) (polynomialEval2621 momentPanelPolynomial2622K03P164)
    (polynomialEval2621 (polynomialDerivative2621 momentPanelPolynomial2622K03P164)) (1 / 200)
    (momentPanelResidualUpper2622K03P164 : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg2622K03P164)
    (by norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPolynomial2622K03P164, polynomialEval2621])
    (fun position _ => polynomialEval_hasDerivAt2621 _ position)
    momentPanelResidual_bound2622K03P164
  rw [momentPanelPolynomial_integral2622K03P164] at hbase
  have hamplitude := (abs_le.mp momentScalarAmp2622K03P164_error).2
  have hgrowth := (abs_le.mp momentScalarGrow2622K03P164_error).2
  rw [← momentBeta_owner2620K03] at hamplitude hgrowth
  have hamplitudeUpper : Real.exp
      (momentPhase2619 (momentBeta2620K03 : ℝ) (149 / 200) 0) ≤
      (momentScalarAmp2622K03P164Expected.1.1 : ℝ) + (momentScalarAmp2622K03P164Expected.2 : ℝ) := by
    linarith
  have hgrowthUpper : Real.exp (2 * momentPhaseSlopeUpper2619 (momentBeta2620K03 : ℝ)
      (149 / 200) (1 / 200) * (1 / 200)) ≤
      (momentScalarGrow2622K03P164Expected.1.1 : ℝ) + (momentScalarGrow2622K03P164Expected.2 : ℝ) := by
    linarith
  have hproduct := mul_le_mul hamplitudeUpper hgrowthUpper
    (le_of_lt (Real.exp_pos _))
    ((le_of_lt (Real.exp_pos _)).trans hamplitudeUpper)
  apply hbase.trans
  have hfactor : 0 ≤ (momentPanelResidualUpper2622K03P164 : ℝ) /
      (1 - (|(149 / 200)| + (1 / 200)) ^ 2) ^ 2 :=
    div_nonneg (Rat.cast_nonneg.mpr momentPanelResidualUpper_nonneg2622K03P164) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hproduct hfactor)
    (by positivity : 0 ≤ (2 : ℝ) * (1 / 200) ^ 2)
  simpa only [momentPanelAnalyticCharge2622K03P164, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using h

theorem actualMomentPanelK03164_integral_certificate2622 :
    |(storedWidth 3 ^ 2) *
      (∫ position in (-(1 / 200))..(1 / 200),
        realNormalizedMomentIntegrand2618 (storedWidth 3 ^ 2) (capturedNodes2584 3).re
          ((149 / 200) + position)) - (momentPanelIntegralCenter2622K03P164 : ℝ)| ≤
      (momentPanelIntegralCharge2622K03P164 : ℝ) := by
  have hphase : (∫ position in (-(1 / 200))..(1 / 200),
      realNormalizedMomentIntegrand2618 (storedWidth 3 ^ 2) (capturedNodes2584 3).re
        ((149 / 200) + position)) =
      (∫ position in (-(1 / 200))..(1 / 200),
        Real.exp (momentPhase2619 (momentBeta2620K03 : ℝ) (149 / 200) position)) := by
    apply intervalIntegral.integral_congr
    intro position hposition
    rw [Set.uIcc_of_le (by norm_num :
      -(1 / 200 : ℝ) ≤
        1 / 200)] at hposition
    rw [momentBeta_owner2620K03]
    exact realNormalizedMomentIntegrand2618_eq_phase2619 _ _ _ _
      (momentPanel_interior2619 (149 / 200) (1 / 200) position (by norm_num) hposition)
  rw [hphase, ← momentRadius_owner2620K03]
  have hcenter : (momentRadius2620K03 : ℝ) * (momentScalarAmp2622K03P164Expected.1.1 : ℝ) *
      (momentPanelIntegral2622K03P164 : ℝ) = (momentPanelIntegralCenter2622K03P164 : ℝ) := by
    exact_mod_cast momentPanelCenter_replay2622K03P164
  have hcharge : (momentRadius2620K03 : ℝ) * ((momentPanelAnalyticCharge2622K03P164 : ℝ) +
      (momentScalarAmp2622K03P164Expected.2 : ℝ) * |(momentPanelIntegral2622K03P164 : ℝ)|) =
      (momentPanelIntegralCharge2622K03P164 : ℝ) := by
    exact_mod_cast momentPanelCharge_replay2622K03P164
  have hamplitude := momentScalarAmp2622K03P164_error
  rw [← momentBeta_owner2620K03] at hamplitude
  have hradius : 0 < (momentRadius2620K03 : ℝ) := by
    rw [momentRadius_owner2620K03]
    exact pow_pos (storedWidth_pos 3) 2
  rw [← hcenter, mul_assoc, ← mul_sub, abs_mul, abs_of_pos hradius]
  apply (mul_le_mul_of_nonneg_left
    ((abs_sub_le _ _ _).trans (add_le_add momentPanelPhase_error2622K03P164
      (show |Real.exp (momentPhase2619 (momentBeta2620K03 : ℝ) (149 / 200) 0) *
          (momentPanelIntegral2622K03P164 : ℝ) - (momentScalarAmp2622K03P164Expected.1.1 : ℝ) *
            (momentPanelIntegral2622K03P164 : ℝ)| ≤
          (momentScalarAmp2622K03P164Expected.2 : ℝ) * |(momentPanelIntegral2622K03P164 : ℝ)| from by
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right hamplitude (abs_nonneg _)))) hradius.le).trans_eq hcharge

theorem actualMomentPanelK03164_integral_error_le2622 :
    |(storedWidth 3 ^ 2) *
      (∫ position in ((37 / 50) : ℝ)..(3 / 4),
        realNormalizedMomentIntegrand2618 (storedWidth 3 ^ 2) (capturedNodes2584 3).re position) -
      (momentPanelIntegralCenter2622K03P164 : ℝ)| ≤ (1 : ℝ) / 10 ^ 72 := by
  have h := actualMomentPanelK03164_integral_certificate2622
  rw [intervalIntegral.integral_comp_add_left] at h
  norm_num only at h
  have hupper : (momentPanelIntegralCharge2622K03P164 : ℝ) ≤
      ((1 / 10 ^ 72 : ℚ) : ℝ) :=
    Rat.cast_le.mpr momentPanelCharge_le2622K03P164
  exact h.trans (by simpa using hupper)

end ConnesWeilRH.Dev
