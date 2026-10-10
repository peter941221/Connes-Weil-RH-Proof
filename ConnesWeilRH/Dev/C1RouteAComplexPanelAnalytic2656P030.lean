import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P030

namespace ConnesWeilRH.Dev

open Set

-- The panel-local phase/derivative lines exceed the 100-character style
-- limit by construction.
set_option linter.style.longLine false

/-!
# Complex analytic containment of panel 030 (record 2656)

Per-panel instance of the record-2649 pilot template: the analytic layer
consuming the record-2648 data tables through the record-2647 generic
stability theorem.  The panel phase is

    phase(u) = (beta + i*psi) * u - 30 / (1 - (center + u)^2),

whose derivative `beta + i*psi - 60*(center + u)/D(u)` satisfies the exact
quotient identity behind the residual replay, so
`|P' - phase' * P| <= residualUpper / deficitLower^2` on the panel.  The
real part of the phase varies by at most (39541 / 63525) on the panel, which turns
the record-2647 stability into the pointwise bound

    ||exp(phase(u) - phase(0)) - P(u)|| <= exp(2*VAR) * residualUpper/DLOW^2 * |u|,

integrated to the panel-local analytic containment certificate.  All
constants are exact rationals derived from the panel center (-129 / 200).
Scope: this panel only.  No off-diagonal claim, no entry containment.
-/

def complexPanelHalfWidth2656P030 : ℚ := 1 / 200

def complexPanelHalfWidthReal2656P030 : ℝ := (complexPanelHalfWidth2656P030 : ℝ)

noncomputable def complexPanelDeficitValue2656P030 (position : ℝ) : ℝ :=
  1 - ((complexPanelCenter2648P030 : ℝ) + position) ^ 2

noncomputable def complexPanelBetaComplex2656P030 : ℂ :=
  ((complexPanelBeta2648P030 : ℝ) : ℂ) + ((complexPanelPsi2648P030 : ℝ) : ℂ) * Complex.I

noncomputable def complexPanelPhase2656P030 (position : ℝ) : ℂ :=
  complexPanelBetaComplex2656P030 * (position : ℂ)
    + Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2656P030 position)

noncomputable def complexPanelPhaseDerivative2656P030 (position : ℝ) : ℂ :=
  complexPanelBetaComplex2656P030
    + Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)
        / complexPanelDeficitValue2656P030 position ^ 2)

theorem complexPanelHalfWidth_nonneg2656P030 : 0 <= complexPanelHalfWidth2656P030 := by
  norm_num [complexPanelHalfWidth2656P030]

theorem complexPanelHalfWidthReal_nonneg2656P030 : 0 <= complexPanelHalfWidthReal2656P030 := by
  norm_num [complexPanelHalfWidthReal2656P030, complexPanelHalfWidth2656P030]

theorem complexPanelBeta_abs_le2656P030 : |complexPanelBeta2648P030| <= 8 := by
  decide +kernel

theorem complexPanelAbsInside2656P030 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :
    |position| <= (1 / 200 : ℝ) := by
  have h := abs_le.mpr ⟨hinside.1, hinside.2⟩
  push_cast at h
  exact h.trans (by norm_num [complexPanelHalfWidthReal2656P030, complexPanelHalfWidth2656P030])

theorem complexPanelDeficit_lower2656P030 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :
    (((231 / 400) : ℝ)) <= complexPanelDeficitValue2656P030 position := by
  have hcenter : ((complexPanelCenter2648P030 : ℝ)) = ((-129 / 200) : ℝ) := by
    norm_num [complexPanelCenter2648P030]
  have habspos : |position| <= (1 / 200 : ℝ) := complexPanelAbsInside2656P030 position hinside
  have hcabs : |((complexPanelCenter2648P030 : ℝ)) + position| <= ((13 / 20) : ℝ) := by
    rw [hcenter]
    calc |((-129 / 200) : ℝ) + position| <= |((-129 / 200) : ℝ)| + |position| := abs_add_le _ _
      _ <= ((13 / 20) : ℝ) := by
            rw [abs_of_neg (by norm_num : ((-129 / 200) : ℝ) < 0)]
            linarith
  obtain ⟨q1, q2⟩ := abs_le.mp hcabs
  have hsq : ((complexPanelCenter2648P030 : ℝ) + position) ^ 2 <= ((13 / 20) : ℝ) ^ 2 := by
    nlinarith
  dsimp only [complexPanelDeficitValue2656P030]
  linarith

theorem complexPanelDeficit_eval2656P030 (position : ℝ) :
    complexPolyEval2647 complexPanelDeficit2648P030 position
      = ((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [complexPolyEval2647, complexPanelDeficit2648P030, embedPair2542,
      complexPanelDeficitValue2656P030, complexPanelCenter2648P030, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      Complex.zero_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelDeficit2648P030, embedPair2542,
      complexPanelDeficitValue2656P030, complexPanelCenter2648P030, Complex.add_im,
      Complex.mul_im, Complex.ofReal_im, Complex.zero_im]
    ring

theorem complexPanelNumerator_eval2656P030 (position : ℝ) :
    complexPolyEval2647 complexPanelNumerator2648P030 position
      = complexPanelBetaComplex2656P030
          * (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2)
        - Complex.ofReal ((60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)) := by
  apply Complex.ext
  · simp only [complexPolyEval2647, complexPanelNumerator2648P030, embedPair2542,
      complexPanelDeficitValue2656P030, complexPanelBetaComplex2656P030,
      complexPanelCenter2648P030, complexPanelBeta2648P030, complexPanelPsi2648P030,
      pow_two, Complex.sub_re, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring
  · simp only [complexPolyEval2647, complexPanelNumerator2648P030, embedPair2542,
      complexPanelDeficitValue2656P030, complexPanelBetaComplex2656P030,
      complexPanelCenter2648P030, complexPanelBeta2648P030, complexPanelPsi2648P030,
      pow_two, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

theorem complexPanelPhaseReal_hasDerivAt2656P030 (position : ℝ)
    (hdeficit : complexPanelDeficitValue2656P030 position ≠ 0) :
    HasDerivAt (fun x : ℝ => (-30 : ℝ) / complexPanelDeficitValue2656P030 x)
      (((-60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)
        / complexPanelDeficitValue2656P030 position ^ 2)) position := by
  have hinner : HasDerivAt (fun x : ℝ => ((complexPanelCenter2648P030 : ℝ) + x))
      (1 : ℝ) position := by
    simpa using (hasDerivAt_const position (complexPanelCenter2648P030 : ℝ)).add
      (hasDerivAt_id position)
  have hdenominator : HasDerivAt
      (fun x : ℝ => (1 : ℝ) - ((complexPanelCenter2648P030 : ℝ) + x) ^ 2)
      ((-2 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)) position := by
    simpa using (hasDerivAt_const position (1 : ℝ)).sub (hinner.pow 2)
  have hquotient : HasDerivAt
      (fun x : ℝ => (-30 : ℝ) / complexPanelDeficitValue2656P030 x)
      (((-30 : ℝ) * -(-2 * ((complexPanelCenter2648P030 : ℝ) + position))) /
        complexPanelDeficitValue2656P030 position ^ 2) position := by
    simpa using (hasDerivAt_const position (-30 : ℝ)).div hdenominator hdeficit
  convert hquotient using 1
  ring

theorem complexPanelPhase_hasDerivAt2656P030 (position : ℝ)
    (hdeficit : complexPanelDeficitValue2656P030 position ≠ 0) :
    HasDerivAt complexPanelPhase2656P030 (complexPanelPhaseDerivative2656P030 position) position := by
  have hreal := complexPanelPhaseReal_hasDerivAt2656P030 position hdeficit
  have hrealC := hreal.ofReal_comp
  have hid : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 position :=
    (hasDerivAt_id position).ofReal_comp
  have hlin : HasDerivAt (fun y : ℝ => complexPanelBetaComplex2656P030 * ((y : ℝ) : ℂ))
      (complexPanelBetaComplex2656P030 * 1) position := HasDerivAt.const_mul _ hid
  have hsum := hlin.add hrealC
  convert hsum using 1
  · dsimp only [complexPanelPhaseDerivative2656P030]
    ring

set_option maxHeartbeats 2000000 in
-- the 57-slot zero-scaled rational fold needs the 2621 heartbeat ceiling
theorem complexPanelPolynomial_zero2656P030 :
    complexPolyEval2647 complexPanelPolynomial2648P030 0 = 1 := by
  rw [← Rat.cast_zero (α := ℝ), complexPolyEval2647_cast]
  have hzero : complexPolyEvalRat2647 0 complexPanelPolynomial2648P030 = (1, 0) := by
    decide +kernel
  rw [hzero, embedPair_one2542]

theorem complexPanelStabilityResidual2656P030 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :
    ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030) position
        - complexPanelPhaseDerivative2656P030 position
            * complexPolyEval2647 complexPanelPolynomial2648P030 position‖
      <= ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ) := by
  have hlower := complexPanelDeficit_lower2656P030 position hinside
  have habs := complexPanelAbsInside2656P030 position hinside
  have hpos : (0 : ℝ) < complexPanelDeficitValue2656P030 position := by linarith
  have hneC : (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ)) ^ 2 ≠ 0 := by
    have hd : ((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]
      exact ne_of_gt hpos
    exact pow_ne_zero 2 hd
  have hom := congrArg (fun L => complexPolyEval2647 L position)
    complexPanelResidual_replay2648P030
  simp only [complexPolyEval2647_add, complexPolyEval2647_mul, complexPolyEval2647_scale,
    complexPanelDeficit_eval2656P030] at hom
  have hneg1 : embedPair2542 (-1, 0) = (-1 : ℂ) := by
    apply Complex.ext <;> simp [embedPair2542]
  rw [hneg1, complexPanelNumerator_eval2656P030] at hom
  push_cast at hom
  have hcanc : Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)
        / complexPanelDeficitValue2656P030 position ^ 2)
      * (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2)
      = Complex.ofReal ((-60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hrel : complexPanelPhaseDerivative2656P030 position
        * (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2)
      = complexPanelBetaComplex2656P030
          * (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2)
        - Complex.ofReal ((60 : ℝ) * ((complexPanelCenter2648P030 : ℝ) + position)) := by
    dsimp only [complexPanelPhaseDerivative2656P030]
    rw [add_mul, hcanc]
    push_cast
    ring
  push_cast at hrel
  have hkey : (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030) position
        - complexPanelPhaseDerivative2656P030 position
            * complexPolyEval2647 complexPanelPolynomial2648P030 position)
        * (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2)
      = complexPolyEval2647 complexPanelResidual2648P030 position := by
    rw [← pow_two] at hom
    rw [sub_mul, mul_right_comm, hrel]
    rw [← hom]
    ring
  have hsplit : complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030) position
        - complexPanelPhaseDerivative2656P030 position
            * complexPolyEval2647 complexPanelPolynomial2648P030 position
      = complexPolyEval2647 complexPanelResidual2648P030 position
          / (((complexPanelDeficitValue2656P030 position : ℝ) : ℂ) ^ 2) := by
    rw [eq_div_iff hneC]
    exact hkey
  have habsQ : |position| <= ((complexPanelHalfWidth2656P030 : ℚ) : ℝ) := by
    norm_num [complexPanelHalfWidth2656P030]
    exact habs
  rw [hsplit, norm_div]
  have habsBound : ‖complexPolyEval2647 complexPanelResidual2648P030 position‖
      <= ((complexPanelResidualUpper2648P030 : ℚ) : ℝ) := by
    rw [← complexPanelResidualUpper_replay2648P030]
    exact complexPolyEval2647_abs_le complexPanelResidual2648P030
      complexPanelHalfWidth2656P030 complexPanelHalfWidth_nonneg2656P030 position habsQ
  have hRUpos : (0 : ℝ) < ((complexPanelResidualUpper2648P030 : ℚ) : ℝ) :=
    Rat.cast_pos.mpr (by norm_num [complexPanelResidualUpper2648P030])
  calc ‖complexPolyEval2647 complexPanelResidual2648P030 position‖
        / ‖(((complexPanelDeficitValue2656P030 position : ℝ)) : ℂ) ^ 2‖
      <= ((complexPanelResidualUpper2648P030 : ℚ) : ℝ)
          / complexPanelDeficitValue2656P030 position ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (div_le_div_iff_of_pos_right (pow_pos hpos 2)).mpr habsBound
    _ <= ((complexPanelResidualUpper2648P030 : ℚ) : ℝ)
          / (((231 / 400) : ℝ)) ^ 2 := by
        exact (div_le_div_iff_of_pos_left hRUpos (pow_pos hpos 2)
          (pow_pos (by norm_num : (0 : ℝ) < ((231 / 400) : ℝ)) 2)).mpr
          (pow_le_pow_left₀ (by norm_num) hlower 2)
    _ = ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ) := by
        norm_num [complexPanelResidualUpper2648P030]

/-! ## Real-part variation of the panel phase -/

theorem complexPanelReVariation2656P030 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :
    |(complexPanelPhase2656P030 position - complexPanelPhase2656P030 0).re| <= ((39541 / 63525) : ℝ) := by
  have hcastC : ((complexPanelCenter2648P030 : ℝ)) = ((-129 / 200) : ℝ) := by
    norm_num [complexPanelCenter2648P030]
  have habs : |position| <= (1 / 200 : ℝ) := complexPanelAbsInside2656P030 position hinside
  have hlower := complexPanelDeficit_lower2656P030 position hinside
  have hpos : (0 : ℝ) < complexPanelDeficitValue2656P030 position := by linarith
  have hapos : (0 : ℝ) < 1 - ((-129 / 200) : ℝ) ^ 2 := by norm_num
  -- |30 * (1/a - 1/d)| <= delta with a = 1 - c^2, d = 1 - (c + position)^2;
  -- the numerator identity is 30*(d - a)/(a*d), NOT 30*(a - d)/(a*d)
  have hR : |(-30 : ℝ) / complexPanelDeficitValue2656P030 position
      + 30 / (1 - ((-129 / 200) : ℝ) ^ 2)| <= ((1480 / 2541) : ℝ) := by
    have hexpr : (-30 : ℝ) / complexPanelDeficitValue2656P030 position
        + 30 / (1 - ((-129 / 200) : ℝ) ^ 2)
        = 30 * (complexPanelDeficitValue2656P030 position - (1 - ((-129 / 200) : ℝ) ^ 2))
          / ((1 - ((-129 / 200) : ℝ) ^ 2) * complexPanelDeficitValue2656P030 position) := by
      field_simp
      ring
    have hdelta : complexPanelDeficitValue2656P030 position - (1 - ((-129 / 200) : ℝ) ^ 2)
        = -((2 * ((-129 / 200) : ℝ) + position) * position) := by
      dsimp only [complexPanelDeficitValue2656P030]
      rw [hcastC]
      ring
    have hprod : (0 : ℝ) < (1 - ((-129 / 200) : ℝ) ^ 2)
        * complexPanelDeficitValue2656P030 position := mul_pos hapos hpos
    have hnum : |(2 * ((-129 / 200) : ℝ) + position) * position|
        <= (((259 / 200) : ℝ)) * (1 / 200 : ℝ) := by
      rw [abs_mul]
      have h1 : |2 * ((-129 / 200) : ℝ) + position| <= (((259 / 200) : ℝ)) := by
        calc |2 * ((-129 / 200) : ℝ) + position|
            <= |2 * ((-129 / 200) : ℝ)| + |position| := abs_add_le _ _
          _ <= (((129 / 100) : ℝ)) + (1 / 200 : ℝ) := by
                rw [abs_of_neg (by norm_num : 2 * ((-129 / 200) : ℝ) < 0)]
                linarith
          _ = (((259 / 200) : ℝ)) := by norm_num
      calc |2 * ((-129 / 200) : ℝ) + position| * |position|
          <= (((259 / 200) : ℝ)) * |position| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg position)
        _ <= (((259 / 200) : ℝ)) * (1 / 200 : ℝ) :=
            mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) <= ((259 / 200) : ℝ))
    have hconst : (30 : ℝ) * (((259 / 200) : ℝ) * (1 / 200 : ℝ))
        <= ((1480 / 2541) : ℝ) * ((1 - ((-129 / 200) : ℝ) ^ 2) * ((231 / 400) : ℝ)) := by norm_num
    rw [hexpr, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 30),
      abs_of_pos hprod, hdelta, abs_neg, div_le_iff₀ hprod]
    refine le_trans (mul_le_mul_of_nonneg_left hnum (by norm_num)) ?_
    refine le_trans hconst ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlower
      (by norm_num : (0 : ℝ) <= 1 - ((-129 / 200) : ℝ) ^ 2))
      (by norm_num : (0 : ℝ) <= ((1480 / 2541) : ℝ))
  -- |beta * position| <= 1/25
  have hbeta8 : |((complexPanelBeta2648P030 : ℝ))| <= (8 : ℝ) := by
    exact_mod_cast complexPanelBeta_abs_le2656P030
  have hbeta : |((complexPanelBeta2648P030 : ℝ)) * position| <= (1 / 25 : ℝ) := by
    calc |((complexPanelBeta2648P030 : ℝ)) * position|
        = |((complexPanelBeta2648P030 : ℝ))| * |position| := abs_mul _ _
      _ <= (8 : ℝ) * |position| :=
          mul_le_mul_of_nonneg_right hbeta8 (abs_nonneg position)
      _ <= (8 : ℝ) * (1 / 200 : ℝ) :=
          mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) <= 8)
      _ <= (1 / 25 : ℝ) := by norm_num
  have htermPos : (complexPanelBetaComplex2656P030 * ((position : ℝ) : ℂ)).re
      = ((complexPanelBeta2648P030 : ℝ)) * position := by
    dsimp only [complexPanelBetaComplex2656P030]
    simp [Complex.mul_re]
  have hterm0 : (complexPanelBetaComplex2656P030 * ((0 : ℝ) : ℂ)).re = 0 := by
    dsimp only [complexPanelBetaComplex2656P030]
    simp
  have hsplit : (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0).re
      = (complexPanelBetaComplex2656P030 * ((position : ℝ) : ℂ)).re
        + (Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2656P030 position)).re
        - (Complex.ofReal ((-30 : ℝ) / complexPanelDeficitValue2656P030 0)).re := by
    dsimp only [complexPanelPhase2656P030]
    simp only [Complex.sub_re, Complex.add_re, hterm0, zero_add]
  have hofRe : ∀ x : ℝ, (Complex.ofReal x).re = x := fun x => by simp
  have hdef0 : complexPanelDeficitValue2656P030 0 = 1 - ((-129 / 200) : ℝ) ^ 2 := by
    dsimp only [complexPanelDeficitValue2656P030]
    rw [hcastC]
    ring
  rw [hsplit, htermPos, hofRe, hofRe, hdef0]
  have hfold : ((complexPanelBeta2648P030 : ℝ)) * position
        + (-30 : ℝ) / complexPanelDeficitValue2656P030 position
        - (-30 : ℝ) / (1 - ((-129 / 200) : ℝ) ^ 2)
      = ((complexPanelBeta2648P030 : ℝ)) * position
        + ((-30 : ℝ) / complexPanelDeficitValue2656P030 position
          + 30 / (1 - ((-129 / 200) : ℝ) ^ 2)) := by
    ring
  rw [hfold]
  calc _ <= |((complexPanelBeta2648P030 : ℝ)) * position|
        + |(-30 : ℝ) / complexPanelDeficitValue2656P030 position
          + 30 / (1 - ((-129 / 200) : ℝ) ^ 2)| := abs_add_le _ _
    _ <= (1 / 25 : ℝ) + ((1480 / 2541) : ℝ) := add_le_add hbeta hR
    _ <= ((39541 / 63525) : ℝ) := by norm_num

/-! ## The generic complex integral error lemma -/

theorem complexExpPolynomialIntegralError2656P030
    (phase phaseDerivative polynomial polynomialDerivative : ℝ → ℂ)
    (halfWidth variation residualUpper : ℝ) (hwidth : 0 <= halfWidth)
    (hpolynomialZero : polynomial 0 = 1)
    (hphaseDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt phase (phaseDerivative position) position)
    (hpolynomialDerivative : ∀ position ∈ Icc (-halfWidth) halfWidth,
      HasDerivAt polynomial (polynomialDerivative position) position)
    (hreVariation : ∀ position ∈ Icc (-halfWidth) halfWidth,
      |(phase position - phase 0).re| <= variation)
    (hresidual : ∀ position ∈ Icc (-halfWidth) halfWidth,
      ‖polynomialDerivative position - phaseDerivative position * polynomial position‖
        <= residualUpper) :
    ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      <= Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by
  have horder : -halfWidth <= halfWidth := by linarith
  have hzero : (0 : ℝ) ∈ Icc (-halfWidth) halfWidth := ⟨by linarith, hwidth⟩
  have hRU : (0 : ℝ) <= residualUpper := (norm_nonneg _).trans (hresidual 0 hzero)
  have hpointwise : ∀ position ∈ Set.uIoc (-halfWidth) halfWidth,
      ‖Complex.exp (phase position - phase 0) - polynomial position‖
        <= Real.exp (2 * variation) * residualUpper * halfWidth := by
    intro position hposition
    rw [Set.uIoc_of_le horder] at hposition
    obtain ⟨hpos1, hpos2⟩ := hposition
    have hclosed : position ∈ Icc (-halfWidth) halfWidth :=
      ⟨le_of_lt hpos1, hpos2⟩
    have habs : |position| <= halfWidth := abs_le.mpr ⟨le_of_lt hpos1, hpos2⟩
    have hstable := complexExpPolynomialResidualStability2647 phase phaseDerivative
      polynomial polynomialDerivative halfWidth variation residualUpper hwidth
      hpolynomialZero hphaseDerivative hpolynomialDerivative hreVariation hresidual
      position hclosed
    exact hstable.trans (mul_le_mul_of_nonneg_left habs
      (mul_nonneg (Real.exp_nonneg _) hRU))
  have hphaseCont : ContinuousOn (fun coordinate => Complex.exp (phase coordinate - phase 0))
      (Icc (-halfWidth) halfWidth) := by
    intro coordinate hcoordinate
    have hsub := (hphaseDerivative coordinate hcoordinate).sub
      (hasDerivAt_const coordinate (phase 0))
    have hsub' : HasDerivAt (fun x => phase x - phase 0)
        (phaseDerivative coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (phase coordinate - phase 0)).comp
      coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn polynomial (Icc (-halfWidth) halfWidth) :=
    HasDerivAt.continuousOn fun coordinate hcoordinate =>
      hpolynomialDerivative coordinate hcoordinate
  have hint : IntervalIntegrable
      (fun coordinate => Complex.exp (phase coordinate - phase 0) - polynomial coordinate)
      MeasureTheory.volume (-halfWidth) halfWidth :=
    (hphaseCont.sub hpolyCont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpointwise
  rw [abs_of_nonneg (by linarith : (0 : ℝ) <= halfWidth - -halfWidth)] at hbound
  calc ‖(∫ position in (-halfWidth)..halfWidth,
        Complex.exp (phase position - phase 0) - polynomial position)‖
      <= Real.exp (2 * variation) * residualUpper * halfWidth
          * (halfWidth - -halfWidth) := hbound
    _ = Real.exp (2 * variation) * residualUpper * (2 * halfWidth ^ 2) := by ring

/-! ## The panel instance and the certificate -/

theorem complexPanelPointwise2656P030 (position : ℝ) (hinside : position ∈ Icc
    (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :
    ‖Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0)
        - complexPolyEval2647 complexPanelPolynomial2648P030 position‖
      <= Real.exp (2 * ((39541 / 63525) : ℝ))
          * ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
          * |position| := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030,
      HasDerivAt complexPanelPhase2656P030
        (complexPanelPhaseDerivative2656P030 coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt2656P030 coordinate ?_
    have hlower := complexPanelDeficit_lower2656P030 coordinate hcoordinate
    linarith
  have hresid : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030,
      ‖complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030) coordinate
          - complexPanelPhaseDerivative2656P030 coordinate
              * complexPolyEval2647 complexPanelPolynomial2648P030 coordinate‖
        <= ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ) :=
    complexPanelStabilityResidual2656P030
  have hkey := complexExpPolynomialResidualStability2647 complexPanelPhase2656P030
    complexPanelPhaseDerivative2656P030
    (complexPolyEval2647 complexPanelPolynomial2648P030)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030))
    complexPanelHalfWidthReal2656P030 ((39541 / 63525) : ℝ)
    ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
    complexPanelHalfWidthReal_nonneg2656P030
    complexPanelPolynomial_zero2656P030 hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P030 coordinate)
    complexPanelReVariation2656P030 hresid position hinside
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelIntegralError2656P030 :
    ‖(∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
        Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0)
          - complexPolyEval2647 complexPanelPolynomial2648P030 position)‖
      <= Real.exp (2 * ((39541 / 63525) : ℝ))
          * ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P030 ^ 2) := by
  have hphaseDeriv : ∀ coordinate ∈ Icc (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030,
      HasDerivAt complexPanelPhase2656P030
        (complexPanelPhaseDerivative2656P030 coordinate) coordinate := by
    intro coordinate hcoordinate
    refine complexPanelPhase_hasDerivAt2656P030 coordinate ?_
    have hlower := complexPanelDeficit_lower2656P030 coordinate hcoordinate
    linarith
  have hresid := complexPanelStabilityResidual2656P030
  have hkey := complexExpPolynomialIntegralError2656P030 complexPanelPhase2656P030
    complexPanelPhaseDerivative2656P030
    (complexPolyEval2647 complexPanelPolynomial2648P030)
    (complexPolyEval2647 (complexPolyDerivative2647 complexPanelPolynomial2648P030))
    complexPanelHalfWidthReal2656P030 ((39541 / 63525) : ℝ)
    ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
    complexPanelHalfWidthReal_nonneg2656P030
    complexPanelPolynomial_zero2656P030 hphaseDeriv
    (fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P030 coordinate)
    complexPanelReVariation2656P030 hresid
  norm_num at hkey ⊢
  exact hkey

theorem complexPanelPolyIntegral2656P030 :
    (∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
      complexPolyEval2647 complexPanelPolynomial2648P030 position)
      = embedPair2542 complexPanelIntegral2648P030 := by
  have horder : -complexPanelHalfWidthReal2656P030 <= complexPanelHalfWidthReal2656P030 := by
    norm_num [complexPanelHalfWidthReal2656P030, complexPanelHalfWidth2656P030]
  have hanti : ∀ coordinate ∈ Set.uIcc (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030,
      HasDerivAt (complexPolyEval2647 complexPanelPrimitive2648P030)
        (complexPolyEval2647 complexPanelPolynomial2648P030 coordinate) coordinate := by
    intro coordinate _
    have h := complexPolyEval2647_hasDerivAt complexPanelPrimitive2648P030 coordinate
    rwa [complexPanelPrimitive_replay2648P030] at h
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P030)
      (Icc (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P030 coordinate
  have hint : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial2648P030) MeasureTheory.volume
      (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030 :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hanti hint
  have hcastPos : complexPolyEval2647 complexPanelPrimitive2648P030
      complexPanelHalfWidthReal2656P030
      = embedPair2542 (complexPolyEvalRat2647 complexPanelHalfWidth2656P030
        complexPanelPrimitive2648P030) := complexPolyEval2647_cast _ _
  have hcastNeg : complexPolyEval2647 complexPanelPrimitive2648P030
      (-complexPanelHalfWidthReal2656P030)
      = embedPair2542 (complexPolyEvalRat2647 (-complexPanelHalfWidth2656P030)
        complexPanelPrimitive2648P030) := by
    have h2 := complexPolyEval2647_cast complexPanelPrimitive2648P030
      (-complexPanelHalfWidth2656P030)
    rwa [Rat.cast_neg] at h2
  rw [hsub, hcastPos, hcastNeg]
  apply Complex.ext
  · simp only [embedPair2542, Complex.sub_re]
    norm_num [complexPanelHalfWidth2656P030]
    exact_mod_cast complexPanelIntegral_re2648P030
  · simp only [embedPair2542, Complex.sub_im]
    norm_num [complexPanelHalfWidth2656P030]
    exact_mod_cast complexPanelIntegral_im2648P030

theorem complexPanelAnalyticCertificate2656P030 :
    ‖(∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
        Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0))‖
      <= ((pairMagnitude2542 complexPanelIntegral2648P030 : ℚ) : ℝ)
        + Real.exp (2 * ((39541 / 63525) : ℝ))
            * ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P030 ^ 2) := by
  have horder : -complexPanelHalfWidthReal2656P030 <= complexPanelHalfWidthReal2656P030 := by
    norm_num [complexPanelHalfWidthReal2656P030, complexPanelHalfWidth2656P030]
  have hphaseCont : ContinuousOn (fun coordinate =>
      Complex.exp (complexPanelPhase2656P030 coordinate - complexPanelPhase2656P030 0))
      (Icc (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) := by
    intro coordinate hcoordinate
    have hd : complexPanelDeficitValue2656P030 coordinate ≠ 0 := by
      have hlower := complexPanelDeficit_lower2656P030 coordinate hcoordinate
      linarith
    have hsub := (complexPanelPhase_hasDerivAt2656P030 coordinate hd).sub
      (hasDerivAt_const coordinate (complexPanelPhase2656P030 0))
    have hsub' : HasDerivAt (fun x => complexPanelPhase2656P030 x - complexPanelPhase2656P030 0)
        (complexPanelPhaseDerivative2656P030 coordinate) coordinate := by
      convert hsub using 1
      ring
    refine ((Complex.hasDerivAt_exp (complexPanelPhase2656P030 coordinate
      - complexPanelPhase2656P030 0)).comp coordinate hsub').continuousAt.continuousWithinAt
  have hpolyCont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P030)
      (Icc (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030) :=
    HasDerivAt.continuousOn fun coordinate _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P030 coordinate
  have hexpInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase2656P030 coordinate - complexPanelPhase2656P030 0))
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030 :=
    hphaseCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hpolyInt : IntervalIntegrable
      (complexPolyEval2647 complexPanelPolynomial2648P030) MeasureTheory.volume
      (-complexPanelHalfWidthReal2656P030) complexPanelHalfWidthReal2656P030 :=
    hpolyCont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hsubInt : IntervalIntegrable (fun coordinate =>
      Complex.exp (complexPanelPhase2656P030 coordinate - complexPanelPhase2656P030 0)
        - complexPolyEval2647 complexPanelPolynomial2648P030 coordinate)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P030)
      complexPanelHalfWidthReal2656P030 := hexpInt.sub hpolyInt
  have herror := complexPanelIntegralError2656P030
  have hfun : (fun coordinate => Complex.exp (complexPanelPhase2656P030 coordinate
          - complexPanelPhase2656P030 0))
      = fun coordinate => (Complex.exp (complexPanelPhase2656P030 coordinate
            - complexPanelPhase2656P030 0)
          - complexPolyEval2647 complexPanelPolynomial2648P030 coordinate)
        + complexPolyEval2647 complexPanelPolynomial2648P030 coordinate := by
    funext coordinate
    ring
  rw [hfun]
  have hintsplit : (∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
        (Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0)
          - complexPolyEval2647 complexPanelPolynomial2648P030 position)
        + complexPolyEval2647 complexPanelPolynomial2648P030 position)
      = (∫ coordinate in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
          Complex.exp (complexPanelPhase2656P030 coordinate - complexPanelPhase2656P030 0)
            - complexPolyEval2647 complexPanelPolynomial2648P030 coordinate)
        + (∫ coordinate in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
            complexPolyEval2647 complexPanelPolynomial2648P030 coordinate) :=
    intervalIntegral.integral_add hsubInt hpolyInt
  rw [hintsplit, complexPanelPolyIntegral2656P030]
  calc ‖(∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
          Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0)
            - complexPolyEval2647 complexPanelPolynomial2648P030 position)
        + embedPair2542 complexPanelIntegral2648P030‖
      <= ‖(∫ position in (-complexPanelHalfWidthReal2656P030)..complexPanelHalfWidthReal2656P030,
            Complex.exp (complexPanelPhase2656P030 position - complexPanelPhase2656P030 0)
              - complexPolyEval2647 complexPanelPolynomial2648P030 position)‖
        + ‖embedPair2542 complexPanelIntegral2648P030‖ := norm_add_le _ _
    _ <= Real.exp (2 * ((39541 / 63525) : ℝ))
          * ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P030 ^ 2)
        + (pairMagnitude2542 complexPanelIntegral2648P030 : ℝ) :=
          add_le_add herror (embedPair_magnitude2542 _)
    _ = ((pairMagnitude2542 complexPanelIntegral2648P030 : ℚ) : ℝ)
        + Real.exp (2 * ((39541 / 63525) : ℝ))
            * ((complexPanelResidualUpper2648P030 / (((231 / 400) : ℚ) ^ 2) : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P030 ^ 2) := by ring

end ConnesWeilRH.Dev
