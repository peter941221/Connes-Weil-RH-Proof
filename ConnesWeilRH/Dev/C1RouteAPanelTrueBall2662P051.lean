import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P051
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P051
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P051
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P051
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P051 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P051 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P051 + panelResidualCharge2662P051.

Scope: entry (0,3), panel P051 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P051 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P051 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P051 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P051 :
    capturedNodes2584 0 = nodeEntry0_2662P051 := rfl

theorem capturedModulations2584_three_eq2662P051 :
    capturedModulations2584 3 = modulationEntry3_2662P051 := rfl

theorem storedWidth_three_eq2662P051 : storedWidth 3 = widthEntry3_2662P051 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P051 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P051 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P051 : ℝ) : ℂ)
        + ((complexPanelPsi2648P051 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P051, capturedModulations2584_three_eq2662P051,
    storedWidth_three_eq2662P051]
  apply Complex.ext
  · simp only [nodeEntry0_2662P051, modulationEntry3_2662P051, widthEntry3_2662P051,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P051, complexPanelPsi2648P051]
  · simp only [nodeEntry0_2662P051, modulationEntry3_2662P051, widthEntry3_2662P051,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P051, complexPanelPsi2648P051]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P051 :
    (complexPanelBeta2648P051 : ℝ) * (complexPanelCenter2648P051 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P051 : ℝ) ^ 2)
      = (ampArg2657P051 : ℝ) := by
  norm_num [complexPanelBeta2648P051, complexPanelCenter2648P051, ampArg2657P051]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P051 :
    (complexPanelPsi2648P051 : ℝ) * (complexPanelCenter2648P051 : ℝ)
      = (phaseArg2658P051 : ℝ) := by
  norm_num [complexPanelPsi2648P051, complexPanelCenter2648P051, phaseArg2658P051]

/-- The record-2656 analytic exponential argument of panel P051. -/
noncomputable def ampExpArg2662P051 : ℝ := 2 * ((2340197 / 9676800) : ℝ)

/-- The record-2656 squared panel deficit of panel P051. -/
def deficitSq2662P051 : ℚ := ((504 / 625 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P051 : ℚ :=
  (ampValue2657P051 + ampRadius2657P051)
    * (2 * ((3 : ℚ) ^ 1 * (complexPanelResidualUpper2648P051 / deficitSq2662P051))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P051). -/
def panelAssemblyCenter2662P051 : RatPair2542 :=
  pairScale2542 ampValue2657P051
    (pairMul2542 phaseValue2658P051 complexPanelIntegral2648P051)

/-- Exact rational assembly charge (panel P051). -/
def panelAssemblyCharge2662P051 : ℚ :=
  ampRadius2657P051 * (pairMagnitude2542 phaseValue2658P051
      + 2 * phaseRadius2658P051)
      * pairMagnitude2542 complexPanelIntegral2648P051
    + (ampValue2657P051 + ampRadius2657P051) * (2 * phaseRadius2658P051)
      * pairMagnitude2542 complexPanelIntegral2648P051

/-- The true panel exponential integral of the P051 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P051 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P051 : ℝ)
        * rotTrue2662 (phaseArg2658P051 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
            Complex.exp (complexPanelPhase2656P051 u - complexPanelPhase2656P051 0))
      - embedPair2542 panelAssemblyCenter2662P051)
    ≤ (panelAssemblyCharge2662P051 : ℝ) + (panelResidualCharge2662P051 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2656P051
      ≤ complexPanelHalfWidthReal2656P051 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P051
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P051)
      complexPanelHalfWidthReal2656P051, HasDerivAt complexPanelPhase2656P051
      (complexPanelPhaseDerivative2656P051 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P051 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P051 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P051 u - complexPanelPhase2656P051 0))
      (Icc (-complexPanelHalfWidthReal2656P051) complexPanelHalfWidthReal2656P051) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P051 x
        - complexPanelPhase2656P051 0)
        (complexPanelPhaseDerivative2656P051 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P051 u
      - complexPanelPhase2656P051 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P051)
      (Icc (-complexPanelHalfWidthReal2656P051) complexPanelHalfWidthReal2656P051) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P051 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P051 u - complexPanelPhase2656P051 0)
      - complexPolyEval2647 complexPanelPolynomial2648P051 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P051)
        complexPanelHalfWidthReal2656P051 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P051)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P051)
        complexPanelHalfWidthReal2656P051 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P051 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P051 : ℝ)
      + (ampRadius2657P051 : ℝ) * (pairMagnitude2542 phaseValue2658P051 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P051 : ℝ)
      ≤ (panelAssemblyCharge2662P051 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P051 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P051])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P051 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P051])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P051 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P051 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P051 : ℝ) * (phaseRadius2658P051 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P051 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P051
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P051)
          * ((complexPanelResidualUpper2648P051 / deficitSq2662P051 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P051 ^ 2)))
      ≤ (panelResidualCharge2662P051 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2656P051 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2656P051, complexPanelHalfWidth2656P051]
    have hexpE : Real.exp (ampExpArg2662P051) ≤ (((3 : ℚ) ^ 1 : ℚ) : ℝ) := by
      unfold ampExpArg2662P051
      exact exp_le_three_pow_rat2662 (2 * ((2340197 / 9676800) : ℝ)) 1 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P051 / deficitSq2662P051 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P051 := by
          norm_num [complexPanelResidualUpper2648P051]
        have h2 : (0 : ℚ) < deficitSq2662P051 := by
          norm_num [deficitSq2662P051]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P051, ampRadius2657P051])
    calc ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P051)
            * ((complexPanelResidualUpper2648P051 / deficitSq2662P051 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P051 ^ 2)))
        = ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P051)
              * ((complexPanelResidualUpper2648P051 / deficitSq2662P051 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P051 + ampRadius2657P051 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 1 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P051 / deficitSq2662P051 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P051 : ℝ) := by
          unfold panelResidualCharge2662P051
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2656P051
    complexPanelPolynomial2648P051
    (ampArg2657P051 : ℝ) (phaseArg2658P051 : ℝ) ampExpArg2662P051
    complexPanelHalfWidthReal2656P051
    ampValue2657P051 ampRadius2657P051 phaseRadius2658P051
    complexPanelResidualUpper2648P051 deficitSq2662P051
    phaseValue2658P051 complexPanelIntegral2648P051
    (panelAssemblyCharge2662P051 : ℝ) (panelResidualCharge2662P051 : ℝ)
    ampPin2657P051 phaseCosPin2658P051 phaseSinPin2658P051
    (by norm_num [ampValue2657P051]) (by norm_num [ampRadius2657P051])
    (by norm_num [phaseRadius2658P051])
    hEint hPint complexPanelPolyIntegral2656P051
    (by
      have h := complexPanelIntegralError2656P051
      simpa [ampExpArg2662P051, deficitSq2662P051] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P051
      = (ampValue2657P051 : ℂ)
        * (embedPair2542 phaseValue2658P051
          * embedPair2542 complexPanelIntegral2648P051) := by
    simp only [panelAssemblyCenter2662P051, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P051. -/
theorem panelCenterNormalization2662P051 :
    (∫ position in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P051 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P051 : ℝ)
        * rotTrue2662 (phaseArg2658P051 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
            Complex.exp (complexPanelPhase2656P051 u - complexPanelPhase2656P051 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P051 : ℝ) (complexPanelPsi2648P051 : ℝ)
    (complexPanelCenter2648P051 : ℝ) complexPanelHalfWidthReal2656P051
    panelBetaTie2662P051 complexPanelHalfWidthReal_nonneg2656P051
    (by
      norm_num [complexPanelCenter2648P051, complexPanelHalfWidthReal2656P051,
        complexPanelHalfWidth2656P051])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P051 : ℝ)
        (complexPanelPsi2648P051 : ℝ) (complexPanelCenter2648P051 : ℝ)
      = ampCenterComplex2662 (ampArg2657P051 : ℝ)
        * rotTrue2662 (phaseArg2658P051 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P051, phaseArgPin2662P051]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P051 : ℝ)
            (complexPanelPsi2648P051 : ℝ) (complexPanelCenter2648P051 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P051 : ℝ)
            (complexPanelPsi2648P051 : ℝ) (complexPanelCenter2648P051 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
            Complex.exp (complexPanelPhase2656P051 u - complexPanelPhase2656P051 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P051 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P051)..complexPanelHalfWidthReal2656P051,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P051 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P051)
      ≤ (panelAssemblyCharge2662P051 : ℝ) + (panelResidualCharge2662P051 : ℝ) := by
  rw [panelCenterNormalization2662P051]
  exact panelValueBall2662P051

#print axioms capturedNodes2584_zero_eq2662P051
#print axioms capturedModulations2584_three_eq2662P051
#print axioms storedWidth_three_eq2662P051
#print axioms panelBetaTie2662P051
#print axioms ampArgPin2662P051
#print axioms phaseArgPin2662P051
#print axioms panelValueBall2662P051
#print axioms panelCenterNormalization2662P051
#print axioms panelTrueBall2662P051

end ConnesWeilRH.Dev
