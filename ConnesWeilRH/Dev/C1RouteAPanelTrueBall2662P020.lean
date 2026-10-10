import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P020
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P020
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P020
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P020
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P020 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P020 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P020 + panelResidualCharge2662P020.

Scope: entry (0,3), panel P020 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P020 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P020 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P020 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P020 :
    capturedNodes2584 0 = nodeEntry0_2662P020 := rfl

theorem capturedModulations2584_three_eq2662P020 :
    capturedModulations2584 3 = modulationEntry3_2662P020 := rfl

theorem storedWidth_three_eq2662P020 : storedWidth 3 = widthEntry3_2662P020 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P020 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P020 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P020 : ℝ) : ℂ)
        + ((complexPanelPsi2648P020 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P020, capturedModulations2584_three_eq2662P020,
    storedWidth_three_eq2662P020]
  apply Complex.ext
  · simp only [nodeEntry0_2662P020, modulationEntry3_2662P020, widthEntry3_2662P020,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P020, complexPanelPsi2648P020]
  · simp only [nodeEntry0_2662P020, modulationEntry3_2662P020, widthEntry3_2662P020,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P020, complexPanelPsi2648P020]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P020 :
    (complexPanelBeta2648P020 : ℝ) * (complexPanelCenter2648P020 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P020 : ℝ) ^ 2)
      = (ampArg2657P020 : ℝ) := by
  norm_num [complexPanelBeta2648P020, complexPanelCenter2648P020, ampArg2657P020]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P020 :
    (complexPanelPsi2648P020 : ℝ) * (complexPanelCenter2648P020 : ℝ)
      = (phaseArg2658P020 : ℝ) := by
  norm_num [complexPanelPsi2648P020, complexPanelCenter2648P020, phaseArg2658P020]

/-- The record-2656 analytic exponential argument of panel P020. -/
noncomputable def ampExpArg2662P020 : ℝ := 2 * ((7421 / 6125) : ℝ)

/-- The record-2656 squared panel deficit of panel P020. -/
def deficitSq2662P020 : ℚ := ((7 / 16 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P020 : ℚ :=
  (ampValue2657P020 + ampRadius2657P020)
    * (2 * ((3 : ℚ) ^ 3 * (complexPanelResidualUpper2648P020 / deficitSq2662P020))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P020). -/
def panelAssemblyCenter2662P020 : RatPair2542 :=
  pairScale2542 ampValue2657P020
    (pairMul2542 phaseValue2658P020 complexPanelIntegral2648P020)

/-- Exact rational assembly charge (panel P020). -/
def panelAssemblyCharge2662P020 : ℚ :=
  ampRadius2657P020 * (pairMagnitude2542 phaseValue2658P020
      + 2 * phaseRadius2658P020)
      * pairMagnitude2542 complexPanelIntegral2648P020
    + (ampValue2657P020 + ampRadius2657P020) * (2 * phaseRadius2658P020)
      * pairMagnitude2542 complexPanelIntegral2648P020

/-- The true panel exponential integral of the P020 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P020 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P020 : ℝ)
        * rotTrue2662 (phaseArg2658P020 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
            Complex.exp (complexPanelPhase2656P020 u - complexPanelPhase2656P020 0))
      - embedPair2542 panelAssemblyCenter2662P020)
    ≤ (panelAssemblyCharge2662P020 : ℝ) + (panelResidualCharge2662P020 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2656P020
      ≤ complexPanelHalfWidthReal2656P020 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P020
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P020)
      complexPanelHalfWidthReal2656P020, HasDerivAt complexPanelPhase2656P020
      (complexPanelPhaseDerivative2656P020 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P020 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P020 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P020 u - complexPanelPhase2656P020 0))
      (Icc (-complexPanelHalfWidthReal2656P020) complexPanelHalfWidthReal2656P020) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P020 x
        - complexPanelPhase2656P020 0)
        (complexPanelPhaseDerivative2656P020 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P020 u
      - complexPanelPhase2656P020 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P020)
      (Icc (-complexPanelHalfWidthReal2656P020) complexPanelHalfWidthReal2656P020) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P020 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P020 u - complexPanelPhase2656P020 0)
      - complexPolyEval2647 complexPanelPolynomial2648P020 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P020)
        complexPanelHalfWidthReal2656P020 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P020)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P020)
        complexPanelHalfWidthReal2656P020 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P020 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P020 : ℝ)
      + (ampRadius2657P020 : ℝ) * (pairMagnitude2542 phaseValue2658P020 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P020 : ℝ)
      ≤ (panelAssemblyCharge2662P020 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P020 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P020])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P020 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P020])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P020 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P020 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P020 : ℝ) * (phaseRadius2658P020 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P020 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P020
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P020)
          * ((complexPanelResidualUpper2648P020 / deficitSq2662P020 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P020 ^ 2)))
      ≤ (panelResidualCharge2662P020 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2656P020 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2656P020, complexPanelHalfWidth2656P020]
    have hexpE : Real.exp (ampExpArg2662P020) ≤ (((3 : ℚ) ^ 3 : ℚ) : ℝ) := by
      unfold ampExpArg2662P020
      exact exp_le_three_pow_rat2662 (2 * ((7421 / 6125) : ℝ)) 3 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P020 / deficitSq2662P020 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P020 := by
          norm_num [complexPanelResidualUpper2648P020]
        have h2 : (0 : ℚ) < deficitSq2662P020 := by
          norm_num [deficitSq2662P020]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P020, ampRadius2657P020])
    calc ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P020)
            * ((complexPanelResidualUpper2648P020 / deficitSq2662P020 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P020 ^ 2)))
        = ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P020)
              * ((complexPanelResidualUpper2648P020 / deficitSq2662P020 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P020 + ampRadius2657P020 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 3 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P020 / deficitSq2662P020 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P020 : ℝ) := by
          unfold panelResidualCharge2662P020
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2656P020
    complexPanelPolynomial2648P020
    (ampArg2657P020 : ℝ) (phaseArg2658P020 : ℝ) ampExpArg2662P020
    complexPanelHalfWidthReal2656P020
    ampValue2657P020 ampRadius2657P020 phaseRadius2658P020
    complexPanelResidualUpper2648P020 deficitSq2662P020
    phaseValue2658P020 complexPanelIntegral2648P020
    (panelAssemblyCharge2662P020 : ℝ) (panelResidualCharge2662P020 : ℝ)
    ampPin2657P020 phaseCosPin2658P020 phaseSinPin2658P020
    (by norm_num [ampValue2657P020]) (by norm_num [ampRadius2657P020])
    (by norm_num [phaseRadius2658P020])
    hEint hPint complexPanelPolyIntegral2656P020
    (by
      have h := complexPanelIntegralError2656P020
      simpa [ampExpArg2662P020, deficitSq2662P020] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P020
      = (ampValue2657P020 : ℂ)
        * (embedPair2542 phaseValue2658P020
          * embedPair2542 complexPanelIntegral2648P020) := by
    simp only [panelAssemblyCenter2662P020, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P020. -/
theorem panelCenterNormalization2662P020 :
    (∫ position in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P020 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P020 : ℝ)
        * rotTrue2662 (phaseArg2658P020 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
            Complex.exp (complexPanelPhase2656P020 u - complexPanelPhase2656P020 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P020 : ℝ) (complexPanelPsi2648P020 : ℝ)
    (complexPanelCenter2648P020 : ℝ) complexPanelHalfWidthReal2656P020
    panelBetaTie2662P020 complexPanelHalfWidthReal_nonneg2656P020
    (by
      norm_num [complexPanelCenter2648P020, complexPanelHalfWidthReal2656P020,
        complexPanelHalfWidth2656P020])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P020 : ℝ)
        (complexPanelPsi2648P020 : ℝ) (complexPanelCenter2648P020 : ℝ)
      = ampCenterComplex2662 (ampArg2657P020 : ℝ)
        * rotTrue2662 (phaseArg2658P020 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P020, phaseArgPin2662P020]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P020 : ℝ)
            (complexPanelPsi2648P020 : ℝ) (complexPanelCenter2648P020 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P020 : ℝ)
            (complexPanelPsi2648P020 : ℝ) (complexPanelCenter2648P020 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
            Complex.exp (complexPanelPhase2656P020 u - complexPanelPhase2656P020 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P020 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P020)..complexPanelHalfWidthReal2656P020,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P020 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P020)
      ≤ (panelAssemblyCharge2662P020 : ℝ) + (panelResidualCharge2662P020 : ℝ) := by
  rw [panelCenterNormalization2662P020]
  exact panelValueBall2662P020

#print axioms capturedNodes2584_zero_eq2662P020
#print axioms capturedModulations2584_three_eq2662P020
#print axioms storedWidth_three_eq2662P020
#print axioms panelBetaTie2662P020
#print axioms ampArgPin2662P020
#print axioms phaseArgPin2662P020
#print axioms panelValueBall2662P020
#print axioms panelCenterNormalization2662P020
#print axioms panelTrueBall2662P020

end ConnesWeilRH.Dev
