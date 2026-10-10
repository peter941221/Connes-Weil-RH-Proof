import ConnesWeilRH.Dev.C1RouteAPanelAssembly2659P095
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P095

/-!
# P095 certified panel ball (record 2660)

Ball-replacement step over the record-2659 pricing audit.  The true panel
integral of the center-normalized exponential multiplied by the true center
amplitude and rotation is enclosed by the exact rational assembly center
plus the corrected product charge plus the record-2656 analytic residual
charge:

  |amp(c) * rot(c) * integral - assembly_center|_1
    <= panelAssemblyCharge2659P095 + panelResidualCharge2660P095.

The record-2658 phase radius is a per-coordinate radius, so the L1
rotation error is at most `2 * phaseRadius2658P095`; the record-2659
charge was corrected in place accordingly.

Scope: this panel and this assembly shape only.  The identity
`integral F = F(c) * integral exp(phase - phase 0)` for the actual entry
integrand, the 190-panel partition sum, and containment in
`analyticMomentInterval2597_row_03` are the next obligations; no producer
GO and no RH claim is made here.
-/

namespace ConnesWeilRH.Dev

open Set

-- The panel-integral lines exceed the 100-character style limit by construction.
set_option linter.style.longLine false

def complexL12660 (z : ℂ) : ℝ := |z.re| + |z.im|

noncomputable def rotTrue2660P095 : ℂ :=
  Complex.exp (Complex.I * ((phaseArg2658P095 : ℝ) : ℂ))

noncomputable def panelIntegralTrue2660P095 : ℂ :=
  ∫ position in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
    Complex.exp (complexPanelPhase2656P095 position - complexPanelPhase2656P095 0)

noncomputable def panelResidualCharge2660P095 : ℝ :=
  ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
    * (2 * (Real.exp (2 * ((11733889 / 277722225) : ℝ))
        * ((complexPanelResidualUpper2648P095 / (((9999 / 10000) : ℚ) ^ 2) : ℚ) : ℝ)
        * (2 * complexPanelHalfWidthReal2656P095 ^ 2)))

-- The real amplitude embedded into ℂ.  Named (not inlined) so that the
-- `.re` / `.im` behavior of the coercion is fixed by rfl lemmas instead of
-- depending on how the elaborator expands the `(x : ℂ)` ascription.
noncomputable def ampCenterComplex2660 : ℂ :=
  Complex.ofReal (Real.exp (ampArg2657P095 : ℝ))

theorem ampCenterComplex_im2660 : ampCenterComplex2660.im = 0 := rfl

theorem ampCenterComplex_re2660 : ampCenterComplex2660.re
    = Real.exp (ampArg2657P095 : ℝ) := rfl

/-! ## Generic L1 lemmas on ℂ -/

theorem complexL1_add_le2660 (z w : ℂ) :
    complexL12660 (z + w) ≤ complexL12660 z + complexL12660 w := by
  simp only [complexL12660, Complex.add_re, Complex.add_im]
  have h1 := abs_add_le z.re w.re
  have h2 := abs_add_le z.im w.im
  linarith

theorem complexL1_mul_le2660 (z w : ℂ) :
    complexL12660 (z * w) ≤ complexL12660 z * complexL12660 w := by
  simp only [complexL12660, Complex.mul_re, Complex.mul_im]
  have hs : |z.re * w.re - z.im * w.im| ≤
      |z.re * w.re| + |z.im * w.im| := abs_sub _ _
  have ha : |z.re * w.im + z.im * w.re| ≤
      |z.re * w.im| + |z.im * w.re| := abs_add_le _ _
  have h1 : |z.re * w.re| ≤ |z.re| * |w.re| := by rw [abs_mul]
  have h2 : |z.im * w.im| ≤ |z.im| * |w.im| := by rw [abs_mul]
  have h3 : |z.re * w.im| ≤ |z.re| * |w.im| := by rw [abs_mul]
  have h4 : |z.im * w.re| ≤ |z.im| * |w.re| := by rw [abs_mul]
  nlinarith [hs, ha, h1, h2, h3, h4, abs_nonneg z.re, abs_nonneg z.im,
    abs_nonneg w.re, abs_nonneg w.im]

theorem complexL1_le_two_norm2660 (z : ℂ) :
    complexL12660 z ≤ (2 : ℝ) * ‖z‖ := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  simp only [complexL12660]
  linarith

theorem complexL1_real_mul2660 (x z : ℂ) (hx : x.im = 0) :
    complexL12660 (x * z) = |x.re| * complexL12660 z := by
  have hre : (x * z).re = x.re * z.re := by
    rw [Complex.mul_re, hx, zero_mul, sub_zero]
  have him : (x * z).im = x.re * z.im := by
    rw [Complex.mul_im, hx, zero_mul, add_zero]
  simp only [complexL12660, hre, him, abs_mul, mul_add]

theorem complexL1_embedPair2660 (a : RatPair2542) :
    complexL12660 (embedPair2542 a) = (pairMagnitude2542 a : ℝ) := by
  simp [complexL12660, embedPair2542, pairMagnitude2542, Rat.cast_abs]

/-! ## The P095 ball -/

theorem panelValueBall2660P095 :
    complexL12660
        (ampCenterComplex2660 * rotTrue2660P095
            * panelIntegralTrue2660P095
          - embedPair2542 panelAssemblyCenter2659P095)
      ≤ (panelAssemblyCharge2659P095 : ℝ) + panelResidualCharge2660P095 := by
  -- pins at the real level
  have hamppos : (0 : ℝ) < Real.exp (ampArg2657P095 : ℝ) := Real.exp_pos _
  have hampabs : |(Real.exp (ampArg2657P095 : ℝ) : ℝ)
      - (ampValue2657P095 : ℝ)| ≤ (ampRadius2657P095 : ℝ) := ampPin2657P095
  obtain ⟨_, hamphi⟩ := abs_le.mp hampabs
  have hcastadd : ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
      = (ampValue2657P095 : ℝ) + (ampRadius2657P095 : ℝ) := Rat.cast_add _ _
  have hampub : (Real.exp (ampArg2657P095 : ℝ) : ℝ)
      ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ) := by linarith
  -- nonnegativity of every rational atom
  have harQ : (0 : ℚ) ≤ ampRadius2657P095 := by norm_num [ampRadius2657P095]
  have havQ : (0 : ℚ) ≤ ampValue2657P095 := by norm_num [ampValue2657P095]
  have havarQ : (0 : ℚ) ≤ ampValue2657P095 + ampRadius2657P095 := by linarith
  have hprQ : (0 : ℚ) ≤ phaseRadius2658P095 := by norm_num [phaseRadius2658P095]
  have hpvQ : (0 : ℚ) ≤ pairMagnitude2542 phaseValue2658P095 := by
    unfold pairMagnitude2542; positivity
  have himQ : (0 : ℚ) ≤ pairMagnitude2542 complexPanelIntegral2648P095 := by
    unfold pairMagnitude2542; positivity
  -- rotation coordinates and norm
  have hrotre : rotTrue2660P095.re = Real.cos (phaseArg2658P095 : ℝ) := by
    rw [rotTrue2660P095]
    exact exp_I_re_cos2646 (phaseArg2658P095 : ℝ)
  have hrotim : rotTrue2660P095.im = Real.sin (phaseArg2658P095 : ℝ) := by
    rw [rotTrue2660P095]
    exact exp_I_im_sin2646 (phaseArg2658P095 : ℝ)
  have hrotnorm : ‖rotTrue2660P095‖ = 1 := by
    rw [rotTrue2660P095, Complex.norm_exp]
    have h0 : (Complex.I * ((phaseArg2658P095 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h0, Real.exp_zero]
  -- L1 of (rotation - embedded phase center) is at most 2 radii
  have hcoord : complexL12660 (rotTrue2660P095
        - embedPair2542 phaseValue2658P095)
      ≤ (2 : ℝ) * (phaseRadius2658P095 : ℝ) := by
    simp only [complexL12660, Complex.sub_re, Complex.sub_im, embedPair2542]
    rw [hrotre, hrotim]
    have h1 := phaseCosPin2658P095
    have h2 := phaseSinPin2658P095
    linarith
  -- integrability of the residual and polynomial integrals
  have horder : -complexPanelHalfWidthReal2656P095
      ≤ complexPanelHalfWidthReal2656P095 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P095
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P095)
      complexPanelHalfWidthReal2656P095, HasDerivAt complexPanelPhase2656P095
      (complexPanelPhaseDerivative2656P095 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P095 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P095 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0))
      (Icc (-complexPanelHalfWidthReal2656P095) complexPanelHalfWidthReal2656P095) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P095 x
        - complexPanelPhase2656P095 0)
        (complexPanelPhaseDerivative2656P095 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P095 u
      - complexPanelPhase2656P095 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P095)
      (Icc (-complexPanelHalfWidthReal2656P095) complexPanelHalfWidthReal2656P095) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P095 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
      - complexPolyEval2647 complexPanelPolynomial2648P095 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P095)
        complexPanelHalfWidthReal2656P095 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P095)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P095)
        complexPanelHalfWidthReal2656P095 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  -- the integral split
  have hadd : (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
        (Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
          - complexPolyEval2647 complexPanelPolynomial2648P095 u)
        + complexPolyEval2647 complexPanelPolynomial2648P095 u)
      = (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
          Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
            - complexPolyEval2647 complexPanelPolynomial2648P095 u)
        + (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
          complexPolyEval2647 complexPanelPolynomial2648P095 u) :=
    intervalIntegral.integral_add hEint hPint
  have hfun : (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
        Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0))
      = (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
          (Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
            - complexPolyEval2647 complexPanelPolynomial2648P095 u)
          + complexPolyEval2647 complexPanelPolynomial2648P095 u) := by
    congr 1
    funext u
    ring
  have hsplit : panelIntegralTrue2660P095
      = (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
          Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
            - complexPolyEval2647 complexPanelPolynomial2648P095 u)
        + embedPair2542 complexPanelIntegral2648P095 := by
    simp only [panelIntegralTrue2660P095]
    rw [← complexPanelPolyIntegral2656P095, ← hadd, hfun]
  -- the analytic residual enclosure
  have hE := complexPanelIntegralError2656P095
  -- piece 1: the residual contribution
  have hp1 : complexL12660 (ampCenterComplex2660 * rotTrue2660P095
        * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
            Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
              - complexPolyEval2647 complexPanelPolynomial2648P095 u))
      ≤ panelResidualCharge2660P095 := by
    unfold panelResidualCharge2660P095
    calc complexL12660 (ampCenterComplex2660 * rotTrue2660P095
            * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u))
        = (Real.exp (ampArg2657P095 : ℝ) : ℝ) * complexL12660 (rotTrue2660P095
            * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u)) := by
          rw [mul_assoc, complexL1_real_mul2660 ampCenterComplex2660
            (rotTrue2660P095 * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u))
            ampCenterComplex_im2660]
          simp only [ampCenterComplex_re2660]
          rw [abs_of_pos hamppos]
      _ ≤ (Real.exp (ampArg2657P095 : ℝ) : ℝ) * (2 * ‖rotTrue2660P095
            * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u)‖) :=
          mul_le_mul_of_nonneg_left (complexL1_le_two_norm2660 _) (le_of_lt hamppos)
      _ ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ) * (2 * ‖rotTrue2660P095
            * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u)‖) :=
          mul_le_mul_of_nonneg_right hampub (by positivity)
      _ = ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
            * (2 * ((1 : ℝ) * ‖(∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
                Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                  - complexPolyEval2647 complexPanelPolynomial2648P095 u)‖)) := by
          rw [Complex.norm_mul, hrotnorm]
      _ ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
            * (2 * (Real.exp (2 * ((11733889 / 277722225) : ℝ))
                * ((complexPanelResidualUpper2648P095 / (((9999 / 10000) : ℚ) ^ 2) : ℚ) : ℝ)
                * (2 * complexPanelHalfWidthReal2656P095 ^ 2))) :=
          mul_le_mul_of_nonneg_left (by linarith [hE])
            (Rat.cast_nonneg.2 havarQ)
  -- piece 2: the center-product contribution
  have hp2 : complexL12660 ((ampCenterComplex2660 * rotTrue2660P095
        - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
      * embedPair2542 complexPanelIntegral2648P095)
      ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ) * (2 : ℝ)
          * (phaseRadius2658P095 : ℝ)
          * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ)
        + (ampRadius2657P095 : ℝ) * (pairMagnitude2542 phaseValue2658P095 : ℝ)
          * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) := by
    have hiMnn : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) :=
      Rat.cast_nonneg.2 himQ
    have hD : complexL12660 (ampCenterComplex2660 * rotTrue2660P095
          - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
        ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
            * ((2 : ℝ) * (phaseRadius2658P095 : ℝ))
          + (ampRadius2657P095 : ℝ) * (pairMagnitude2542 phaseValue2658P095 : ℝ) := by
      have hsplitD : ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095
          = ampCenterComplex2660
              * (rotTrue2660P095 - embedPair2542 phaseValue2658P095)
            + (ampCenterComplex2660 - (ampValue2657P095 : ℂ))
              * embedPair2542 phaseValue2658P095 := by ring
      have hA : complexL12660 (ampCenterComplex2660
            * (rotTrue2660P095 - embedPair2542 phaseValue2658P095))
          ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRadius2658P095 : ℝ)) := by
        calc complexL12660 (ampCenterComplex2660
                * (rotTrue2660P095 - embedPair2542 phaseValue2658P095))
            = (Real.exp (ampArg2657P095 : ℝ) : ℝ)
                * complexL12660 (rotTrue2660P095
                  - embedPair2542 phaseValue2658P095) := by
              rw [complexL1_real_mul2660 ampCenterComplex2660
                (rotTrue2660P095 - embedPair2542 phaseValue2658P095)
                ampCenterComplex_im2660]
              simp only [ampCenterComplex_re2660]
              rw [abs_of_pos hamppos]
          _ ≤ (Real.exp (ampArg2657P095 : ℝ) : ℝ)
                * ((2 : ℝ) * (phaseRadius2658P095 : ℝ)) :=
              mul_le_mul_of_nonneg_left hcoord (le_of_lt hamppos)
          _ ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
                * ((2 : ℝ) * (phaseRadius2658P095 : ℝ)) :=
              mul_le_mul_of_nonneg_right hampub (by positivity)
      have hB : complexL12660 ((ampCenterComplex2660
            - (ampValue2657P095 : ℂ)) * embedPair2542 phaseValue2658P095)
          ≤ (ampRadius2657P095 : ℝ)
              * (pairMagnitude2542 phaseValue2658P095 : ℝ) := by
        have hz0 : (ampCenterComplex2660
            - (ampValue2657P095 : ℂ)).im = 0 := by
          rw [Complex.sub_im, ampCenterComplex_im2660]
          simp
        calc complexL12660 ((ampCenterComplex2660
                - (ampValue2657P095 : ℂ)) * embedPair2542 phaseValue2658P095)
            = |(ampCenterComplex2660
                - (ampValue2657P095 : ℂ)).re|
                * complexL12660 (embedPair2542 phaseValue2658P095) :=
              complexL1_real_mul2660 _ _ hz0
          _ = |(Real.exp (ampArg2657P095 : ℝ) : ℝ) - (ampValue2657P095 : ℝ)|
                * complexL12660 (embedPair2542 phaseValue2658P095) := by
              simp only [Complex.sub_re, ampCenterComplex_re2660, Complex.ratCast_re]
          _ ≤ (ampRadius2657P095 : ℝ)
                * complexL12660 (embedPair2542 phaseValue2658P095) :=
              mul_le_mul_of_nonneg_right hampabs
                (by simp only [complexL12660]; positivity)
          _ = (ampRadius2657P095 : ℝ)
                * (pairMagnitude2542 phaseValue2658P095 : ℝ) := by
              rw [complexL1_embedPair2660]
      calc complexL12660 (ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          = complexL12660 (ampCenterComplex2660
                * (rotTrue2660P095 - embedPair2542 phaseValue2658P095)
              + (ampCenterComplex2660 - (ampValue2657P095 : ℂ))
                * embedPair2542 phaseValue2658P095) := by rw [hsplitD]
        _ ≤ complexL12660 (ampCenterComplex2660
                * (rotTrue2660P095 - embedPair2542 phaseValue2658P095))
            + complexL12660 ((ampCenterComplex2660
              - (ampValue2657P095 : ℂ)) * embedPair2542 phaseValue2658P095) :=
          complexL1_add_le2660 _ _
        _ ≤ ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRadius2658P095 : ℝ))
            + (ampRadius2657P095 : ℝ)
              * (pairMagnitude2542 phaseValue2658P095 : ℝ) := add_le_add hA hB
    calc complexL12660 ((ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * embedPair2542 complexPanelIntegral2648P095)
        ≤ complexL12660 (ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * complexL12660 (embedPair2542 complexPanelIntegral2648P095) :=
          complexL1_mul_le2660 _ _
      _ = complexL12660 (ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) := by
          rw [complexL1_embedPair2660]
      _ ≤ (((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ)
              * ((2 : ℝ) * (phaseRadius2658P095 : ℝ))
            + (ampRadius2657P095 : ℝ)
              * (pairMagnitude2542 phaseValue2658P095 : ℝ))
          * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) :=
          mul_le_mul_of_nonneg_right hD hiMnn
      _ = ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ) * (2 : ℝ)
            * (phaseRadius2658P095 : ℝ)
            * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ)
          + (ampRadius2657P095 : ℝ) * (pairMagnitude2542 phaseValue2658P095 : ℝ)
            * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) := by ring
  -- the charge covers the product bound
  have hcharge : ((ampValue2657P095 + ampRadius2657P095 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P095 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ)
      + (ampRadius2657P095 : ℝ) * (pairMagnitude2542 phaseValue2658P095 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ)
      ≤ (panelAssemblyCharge2659P095 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P095 : ℝ) := Rat.cast_nonneg.2 harQ
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P095 : ℝ) := Rat.cast_nonneg.2 hprQ
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P095 : ℝ) :=
      Rat.cast_nonneg.2 hpvQ
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) :=
      Rat.cast_nonneg.2 himQ
    have hthree : (0 : ℝ) ≤ (ampRadius2657P095 : ℝ) * (phaseRadius2658P095 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P095 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2659P095
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  -- assembly center in product form and the final decomposition
  have hcenterC : embedPair2542 panelAssemblyCenter2659P095
      = (ampValue2657P095 : ℂ)
        * (embedPair2542 phaseValue2658P095
          * embedPair2542 complexPanelIntegral2648P095) := by
    simp only [panelAssemblyCenter2659P095, embedPair_scale2542, embedPair_mul2542]
  rw [hsplit, hcenterC]
  have hdecomp : ampCenterComplex2660 * rotTrue2660P095
        * ((∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
            Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
              - complexPolyEval2647 complexPanelPolynomial2648P095 u)
          + embedPair2542 complexPanelIntegral2648P095)
      - (ampValue2657P095 : ℂ)
        * (embedPair2542 phaseValue2658P095
          * embedPair2542 complexPanelIntegral2648P095)
      = ampCenterComplex2660 * rotTrue2660P095
        * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
            Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
              - complexPolyEval2647 complexPanelPolynomial2648P095 u)
        + (ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * embedPair2542 complexPanelIntegral2648P095 := by
    ring
  rw [hdecomp]
  have hstep : complexL12660 (ampCenterComplex2660 * rotTrue2660P095
        * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
            Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
              - complexPolyEval2647 complexPanelPolynomial2648P095 u)
        + (ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * embedPair2542 complexPanelIntegral2648P095)
      ≤ complexL12660 (ampCenterComplex2660 * rotTrue2660P095
          * (∫ u in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
              Complex.exp (complexPanelPhase2656P095 u - complexPanelPhase2656P095 0)
                - complexPolyEval2647 complexPanelPolynomial2648P095 u))
        + complexL12660 ((ampCenterComplex2660 * rotTrue2660P095
            - (ampValue2657P095 : ℂ) * embedPair2542 phaseValue2658P095)
          * embedPair2542 complexPanelIntegral2648P095) :=
    complexL1_add_le2660 _ _
  linarith [hstep, hp1, hp2, hcharge]

#print axioms complexL1_add_le2660
#print axioms complexL1_mul_le2660
#print axioms complexL1_le_two_norm2660
#print axioms complexL1_real_mul2660
#print axioms complexL1_embedPair2660
#print axioms ampCenterComplex_im2660
#print axioms ampCenterComplex_re2660
#print axioms panelValueBall2660P095

end ConnesWeilRH.Dev
