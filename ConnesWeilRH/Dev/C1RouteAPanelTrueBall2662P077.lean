import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P077
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P077
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P077
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P077
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P077 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P077 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P077 + panelResidualCharge2662P077.

Scope: entry (0,3), panel P077 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P077 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P077 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P077 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P077 :
    capturedNodes2584 0 = nodeEntry0_2662P077 := rfl

theorem capturedModulations2584_three_eq2662P077 :
    capturedModulations2584 3 = modulationEntry3_2662P077 := rfl

theorem storedWidth_three_eq2662P077 : storedWidth 3 = widthEntry3_2662P077 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P077 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P077 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P077 : ℝ) : ℂ)
        + ((complexPanelPsi2648P077 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P077, capturedModulations2584_three_eq2662P077,
    storedWidth_three_eq2662P077]
  apply Complex.ext
  · simp only [nodeEntry0_2662P077, modulationEntry3_2662P077, widthEntry3_2662P077,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P077, complexPanelPsi2648P077]
  · simp only [nodeEntry0_2662P077, modulationEntry3_2662P077, widthEntry3_2662P077,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P077, complexPanelPsi2648P077]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P077 :
    (complexPanelBeta2648P077 : ℝ) * (complexPanelCenter2648P077 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P077 : ℝ) ^ 2)
      = (ampArg2657P077 : ℝ) := by
  norm_num [complexPanelBeta2648P077, complexPanelCenter2648P077, ampArg2657P077]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P077 :
    (complexPanelPsi2648P077 : ℝ) * (complexPanelCenter2648P077 : ℝ)
      = (phaseArg2658P077 : ℝ) := by
  norm_num [complexPanelPsi2648P077, complexPanelCenter2648P077, phaseArg2658P077]

/-- The record-2656 analytic exponential argument of panel P077. -/
noncomputable def ampExpArg2662P077 : ℝ := 2 * ((28343747 / 292578050) : ℝ)

/-- The record-2656 squared panel deficit of panel P077. -/
def deficitSq2662P077 : ℚ := ((2419 / 2500 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P077 : ℚ :=
  (ampValue2657P077 + ampRadius2657P077)
    * (2 * ((3 : ℚ) ^ 1 * (complexPanelResidualUpper2648P077 / deficitSq2662P077))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P077). -/
def panelAssemblyCenter2662P077 : RatPair2542 :=
  pairScale2542 ampValue2657P077
    (pairMul2542 phaseValue2658P077 complexPanelIntegral2648P077)

/-- Exact rational assembly charge (panel P077). -/
def panelAssemblyCharge2662P077 : ℚ :=
  ampRadius2657P077 * (pairMagnitude2542 phaseValue2658P077
      + 2 * phaseRadius2658P077)
      * pairMagnitude2542 complexPanelIntegral2648P077
    + (ampValue2657P077 + ampRadius2657P077) * (2 * phaseRadius2658P077)
      * pairMagnitude2542 complexPanelIntegral2648P077

/-- The true panel exponential integral of the P077 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P077 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P077 : ℝ)
        * rotTrue2662 (phaseArg2658P077 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
            Complex.exp (complexPanelPhase2656P077 u - complexPanelPhase2656P077 0))
      - embedPair2542 panelAssemblyCenter2662P077)
    ≤ (panelAssemblyCharge2662P077 : ℝ) + (panelResidualCharge2662P077 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2656P077
      ≤ complexPanelHalfWidthReal2656P077 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P077
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P077)
      complexPanelHalfWidthReal2656P077, HasDerivAt complexPanelPhase2656P077
      (complexPanelPhaseDerivative2656P077 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P077 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P077 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P077 u - complexPanelPhase2656P077 0))
      (Icc (-complexPanelHalfWidthReal2656P077) complexPanelHalfWidthReal2656P077) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P077 x
        - complexPanelPhase2656P077 0)
        (complexPanelPhaseDerivative2656P077 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P077 u
      - complexPanelPhase2656P077 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P077)
      (Icc (-complexPanelHalfWidthReal2656P077) complexPanelHalfWidthReal2656P077) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P077 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P077 u - complexPanelPhase2656P077 0)
      - complexPolyEval2647 complexPanelPolynomial2648P077 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P077)
        complexPanelHalfWidthReal2656P077 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P077)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P077)
        complexPanelHalfWidthReal2656P077 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P077 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P077 : ℝ)
      + (ampRadius2657P077 : ℝ) * (pairMagnitude2542 phaseValue2658P077 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P077 : ℝ)
      ≤ (panelAssemblyCharge2662P077 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P077 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P077])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P077 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P077])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P077 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P077 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P077 : ℝ) * (phaseRadius2658P077 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P077 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P077
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P077)
          * ((complexPanelResidualUpper2648P077 / deficitSq2662P077 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P077 ^ 2)))
      ≤ (panelResidualCharge2662P077 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2656P077 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2656P077, complexPanelHalfWidth2656P077]
    have hexpE : Real.exp (ampExpArg2662P077) ≤ (((3 : ℚ) ^ 1 : ℚ) : ℝ) := by
      unfold ampExpArg2662P077
      exact exp_le_three_pow_rat2662 (2 * ((28343747 / 292578050) : ℝ)) 1 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P077 / deficitSq2662P077 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P077 := by
          norm_num [complexPanelResidualUpper2648P077]
        have h2 : (0 : ℚ) < deficitSq2662P077 := by
          norm_num [deficitSq2662P077]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P077, ampRadius2657P077])
    calc ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P077)
            * ((complexPanelResidualUpper2648P077 / deficitSq2662P077 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P077 ^ 2)))
        = ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P077)
              * ((complexPanelResidualUpper2648P077 / deficitSq2662P077 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P077 + ampRadius2657P077 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 1 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P077 / deficitSq2662P077 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P077 : ℝ) := by
          unfold panelResidualCharge2662P077
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2656P077
    complexPanelPolynomial2648P077
    (ampArg2657P077 : ℝ) (phaseArg2658P077 : ℝ) ampExpArg2662P077
    complexPanelHalfWidthReal2656P077
    ampValue2657P077 ampRadius2657P077 phaseRadius2658P077
    complexPanelResidualUpper2648P077 deficitSq2662P077
    phaseValue2658P077 complexPanelIntegral2648P077
    (panelAssemblyCharge2662P077 : ℝ) (panelResidualCharge2662P077 : ℝ)
    ampPin2657P077 phaseCosPin2658P077 phaseSinPin2658P077
    (by norm_num [ampValue2657P077]) (by norm_num [ampRadius2657P077])
    (by norm_num [phaseRadius2658P077])
    hEint hPint complexPanelPolyIntegral2656P077
    (by
      have h := complexPanelIntegralError2656P077
      simpa [ampExpArg2662P077, deficitSq2662P077] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P077
      = (ampValue2657P077 : ℂ)
        * (embedPair2542 phaseValue2658P077
          * embedPair2542 complexPanelIntegral2648P077) := by
    simp only [panelAssemblyCenter2662P077, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P077. -/
theorem panelCenterNormalization2662P077 :
    (∫ position in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P077 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P077 : ℝ)
        * rotTrue2662 (phaseArg2658P077 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
            Complex.exp (complexPanelPhase2656P077 u - complexPanelPhase2656P077 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P077 : ℝ) (complexPanelPsi2648P077 : ℝ)
    (complexPanelCenter2648P077 : ℝ) complexPanelHalfWidthReal2656P077
    panelBetaTie2662P077 complexPanelHalfWidthReal_nonneg2656P077
    (by
      norm_num [complexPanelCenter2648P077, complexPanelHalfWidthReal2656P077,
        complexPanelHalfWidth2656P077])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P077 : ℝ)
        (complexPanelPsi2648P077 : ℝ) (complexPanelCenter2648P077 : ℝ)
      = ampCenterComplex2662 (ampArg2657P077 : ℝ)
        * rotTrue2662 (phaseArg2658P077 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P077, phaseArgPin2662P077]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P077 : ℝ)
            (complexPanelPsi2648P077 : ℝ) (complexPanelCenter2648P077 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P077 : ℝ)
            (complexPanelPsi2648P077 : ℝ) (complexPanelCenter2648P077 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
            Complex.exp (complexPanelPhase2656P077 u - complexPanelPhase2656P077 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P077 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P077)..complexPanelHalfWidthReal2656P077,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P077 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P077)
      ≤ (panelAssemblyCharge2662P077 : ℝ) + (panelResidualCharge2662P077 : ℝ) := by
  rw [panelCenterNormalization2662P077]
  exact panelValueBall2662P077

#print axioms capturedNodes2584_zero_eq2662P077
#print axioms capturedModulations2584_three_eq2662P077
#print axioms storedWidth_three_eq2662P077
#print axioms panelBetaTie2662P077
#print axioms ampArgPin2662P077
#print axioms phaseArgPin2662P077
#print axioms panelValueBall2662P077
#print axioms panelCenterNormalization2662P077
#print axioms panelTrueBall2662P077

end ConnesWeilRH.Dev
