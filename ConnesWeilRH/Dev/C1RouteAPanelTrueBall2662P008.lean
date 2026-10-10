import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P008
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P008
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P008
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P008
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P008 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P008 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P008 + panelResidualCharge2662P008.

Scope: entry (0,3), panel P008 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P008 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P008 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P008 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P008 :
    capturedNodes2584 0 = nodeEntry0_2662P008 := rfl

theorem capturedModulations2584_three_eq2662P008 :
    capturedModulations2584 3 = modulationEntry3_2662P008 := rfl

theorem storedWidth_three_eq2662P008 : storedWidth 3 = widthEntry3_2662P008 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P008 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P008 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P008 : ℝ) : ℂ)
        + ((complexPanelPsi2648P008 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P008, capturedModulations2584_three_eq2662P008,
    storedWidth_three_eq2662P008]
  apply Complex.ext
  · simp only [nodeEntry0_2662P008, modulationEntry3_2662P008, widthEntry3_2662P008,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P008, complexPanelPsi2648P008]
  · simp only [nodeEntry0_2662P008, modulationEntry3_2662P008, widthEntry3_2662P008,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P008, complexPanelPsi2648P008]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P008 :
    (complexPanelBeta2648P008 : ℝ) * (complexPanelCenter2648P008 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P008 : ℝ) ^ 2)
      = (ampArg2657P008 : ℝ) := by
  norm_num [complexPanelBeta2648P008, complexPanelCenter2648P008, ampArg2657P008]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P008 :
    (complexPanelPsi2648P008 : ℝ) * (complexPanelCenter2648P008 : ℝ)
      = (phaseArg2658P008 : ℝ) := by
  norm_num [complexPanelPsi2648P008, complexPanelCenter2648P008, phaseArg2658P008]

/-- The record-2656 analytic exponential argument of panel P008. -/
noncomputable def ampExpArg2662P008 : ℝ := 2 * ((656534761 / 147744025) : ℝ)

/-- The record-2656 squared panel deficit of panel P008. -/
def deficitSq2662P008 : ℚ := ((2431 / 10000 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P008 : ℚ :=
  (ampValue2657P008 + ampRadius2657P008)
    * (2 * ((3 : ℚ) ^ 9 * (complexPanelResidualUpper2648P008 / deficitSq2662P008))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P008). -/
def panelAssemblyCenter2662P008 : RatPair2542 :=
  pairScale2542 ampValue2657P008
    (pairMul2542 phaseValue2658P008 complexPanelIntegral2648P008)

/-- Exact rational assembly charge (panel P008). -/
def panelAssemblyCharge2662P008 : ℚ :=
  ampRadius2657P008 * (pairMagnitude2542 phaseValue2658P008
      + 2 * phaseRadius2658P008)
      * pairMagnitude2542 complexPanelIntegral2648P008
    + (ampValue2657P008 + ampRadius2657P008) * (2 * phaseRadius2658P008)
      * pairMagnitude2542 complexPanelIntegral2648P008

/-- The true panel exponential integral of the P008 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P008 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P008 : ℝ)
        * rotTrue2662 (phaseArg2658P008 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
            Complex.exp (complexPanelPhase2656P008 u - complexPanelPhase2656P008 0))
      - embedPair2542 panelAssemblyCenter2662P008)
    ≤ (panelAssemblyCharge2662P008 : ℝ) + (panelResidualCharge2662P008 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2656P008
      ≤ complexPanelHalfWidthReal2656P008 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P008
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P008)
      complexPanelHalfWidthReal2656P008, HasDerivAt complexPanelPhase2656P008
      (complexPanelPhaseDerivative2656P008 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P008 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P008 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P008 u - complexPanelPhase2656P008 0))
      (Icc (-complexPanelHalfWidthReal2656P008) complexPanelHalfWidthReal2656P008) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P008 x
        - complexPanelPhase2656P008 0)
        (complexPanelPhaseDerivative2656P008 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P008 u
      - complexPanelPhase2656P008 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P008)
      (Icc (-complexPanelHalfWidthReal2656P008) complexPanelHalfWidthReal2656P008) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P008 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P008 u - complexPanelPhase2656P008 0)
      - complexPolyEval2647 complexPanelPolynomial2648P008 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P008)
        complexPanelHalfWidthReal2656P008 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P008)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P008)
        complexPanelHalfWidthReal2656P008 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P008 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P008 : ℝ)
      + (ampRadius2657P008 : ℝ) * (pairMagnitude2542 phaseValue2658P008 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P008 : ℝ)
      ≤ (panelAssemblyCharge2662P008 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P008 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P008])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P008 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P008])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P008 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P008 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P008 : ℝ) * (phaseRadius2658P008 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P008 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P008
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P008)
          * ((complexPanelResidualUpper2648P008 / deficitSq2662P008 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P008 ^ 2)))
      ≤ (panelResidualCharge2662P008 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2656P008 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2656P008, complexPanelHalfWidth2656P008]
    have hexpE : Real.exp (ampExpArg2662P008) ≤ (((3 : ℚ) ^ 9 : ℚ) : ℝ) := by
      unfold ampExpArg2662P008
      exact exp_le_three_pow_rat2662 (2 * ((656534761 / 147744025) : ℝ)) 9 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P008 / deficitSq2662P008 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P008 := by
          norm_num [complexPanelResidualUpper2648P008]
        have h2 : (0 : ℚ) < deficitSq2662P008 := by
          norm_num [deficitSq2662P008]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P008, ampRadius2657P008])
    calc ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P008)
            * ((complexPanelResidualUpper2648P008 / deficitSq2662P008 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P008 ^ 2)))
        = ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P008)
              * ((complexPanelResidualUpper2648P008 / deficitSq2662P008 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P008 + ampRadius2657P008 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 9 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P008 / deficitSq2662P008 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P008 : ℝ) := by
          unfold panelResidualCharge2662P008
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2656P008
    complexPanelPolynomial2648P008
    (ampArg2657P008 : ℝ) (phaseArg2658P008 : ℝ) ampExpArg2662P008
    complexPanelHalfWidthReal2656P008
    ampValue2657P008 ampRadius2657P008 phaseRadius2658P008
    complexPanelResidualUpper2648P008 deficitSq2662P008
    phaseValue2658P008 complexPanelIntegral2648P008
    (panelAssemblyCharge2662P008 : ℝ) (panelResidualCharge2662P008 : ℝ)
    ampPin2657P008 phaseCosPin2658P008 phaseSinPin2658P008
    (by norm_num [ampValue2657P008]) (by norm_num [ampRadius2657P008])
    (by norm_num [phaseRadius2658P008])
    hEint hPint complexPanelPolyIntegral2656P008
    (by
      have h := complexPanelIntegralError2656P008
      simpa [ampExpArg2662P008, deficitSq2662P008] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P008
      = (ampValue2657P008 : ℂ)
        * (embedPair2542 phaseValue2658P008
          * embedPair2542 complexPanelIntegral2648P008) := by
    simp only [panelAssemblyCenter2662P008, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P008. -/
theorem panelCenterNormalization2662P008 :
    (∫ position in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P008 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P008 : ℝ)
        * rotTrue2662 (phaseArg2658P008 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
            Complex.exp (complexPanelPhase2656P008 u - complexPanelPhase2656P008 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P008 : ℝ) (complexPanelPsi2648P008 : ℝ)
    (complexPanelCenter2648P008 : ℝ) complexPanelHalfWidthReal2656P008
    panelBetaTie2662P008 complexPanelHalfWidthReal_nonneg2656P008
    (by
      norm_num [complexPanelCenter2648P008, complexPanelHalfWidthReal2656P008,
        complexPanelHalfWidth2656P008])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P008 : ℝ)
        (complexPanelPsi2648P008 : ℝ) (complexPanelCenter2648P008 : ℝ)
      = ampCenterComplex2662 (ampArg2657P008 : ℝ)
        * rotTrue2662 (phaseArg2658P008 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P008, phaseArgPin2662P008]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P008 : ℝ)
            (complexPanelPsi2648P008 : ℝ) (complexPanelCenter2648P008 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P008 : ℝ)
            (complexPanelPsi2648P008 : ℝ) (complexPanelCenter2648P008 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
            Complex.exp (complexPanelPhase2656P008 u - complexPanelPhase2656P008 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P008 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P008)..complexPanelHalfWidthReal2656P008,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P008 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P008)
      ≤ (panelAssemblyCharge2662P008 : ℝ) + (panelResidualCharge2662P008 : ℝ) := by
  rw [panelCenterNormalization2662P008]
  exact panelValueBall2662P008

#print axioms capturedNodes2584_zero_eq2662P008
#print axioms capturedModulations2584_three_eq2662P008
#print axioms storedWidth_three_eq2662P008
#print axioms panelBetaTie2662P008
#print axioms ampArgPin2662P008
#print axioms phaseArgPin2662P008
#print axioms panelValueBall2662P008
#print axioms panelCenterNormalization2662P008
#print axioms panelTrueBall2662P008

end ConnesWeilRH.Dev
