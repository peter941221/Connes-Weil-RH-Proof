import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P109
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P109
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2648P109
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2649P109
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P109 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P109 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P109 + panelResidualCharge2662P109.

Scope: entry (0,3), panel P109 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P109 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P109 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P109 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P109 :
    capturedNodes2584 0 = nodeEntry0_2662P109 := rfl

theorem capturedModulations2584_three_eq2662P109 :
    capturedModulations2584 3 = modulationEntry3_2662P109 := rfl

theorem storedWidth_three_eq2662P109 : storedWidth 3 = widthEntry3_2662P109 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P109 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P109 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P109 : ℝ) : ℂ)
        + ((complexPanelPsi2648P109 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P109, capturedModulations2584_three_eq2662P109,
    storedWidth_three_eq2662P109]
  apply Complex.ext
  · simp only [nodeEntry0_2662P109, modulationEntry3_2662P109, widthEntry3_2662P109,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P109, complexPanelPsi2648P109]
  · simp only [nodeEntry0_2662P109, modulationEntry3_2662P109, widthEntry3_2662P109,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P109, complexPanelPsi2648P109]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P109 :
    (complexPanelBeta2648P109 : ℝ) * (complexPanelCenter2648P109 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P109 : ℝ) ^ 2)
      = (ampArg2657P109 : ℝ) := by
  norm_num [complexPanelBeta2648P109, complexPanelCenter2648P109, ampArg2657P109]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P109 :
    (complexPanelPsi2648P109 : ℝ) * (complexPanelCenter2648P109 : ℝ)
      = (phaseArg2658P109 : ℝ) := by
  norm_num [complexPanelPsi2648P109, complexPanelCenter2648P109, phaseArg2658P109]

/-- The record-2656 analytic exponential argument of panel P109. -/
noncomputable def ampExpArg2662P109 : ℝ := ((1 / 5) : ℝ)

/-- The record-2656 squared panel deficit of panel P109. -/
def deficitSq2662P109 : ℚ := ((391 / 400 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P109 : ℚ :=
  (ampValue2657P109 + ampRadius2657P109)
    * (2 * ((3 : ℚ) ^ 1 * (complexPanelResidualUpper2648P109 / deficitSq2662P109))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P109). -/
def panelAssemblyCenter2662P109 : RatPair2542 :=
  pairScale2542 ampValue2657P109
    (pairMul2542 phaseValue2658P109 complexPanelIntegral2648P109)

/-- Exact rational assembly charge (panel P109). -/
def panelAssemblyCharge2662P109 : ℚ :=
  ampRadius2657P109 * (pairMagnitude2542 phaseValue2658P109
      + 2 * phaseRadius2658P109)
      * pairMagnitude2542 complexPanelIntegral2648P109
    + (ampValue2657P109 + ampRadius2657P109) * (2 * phaseRadius2658P109)
      * pairMagnitude2542 complexPanelIntegral2648P109

/-- The true panel exponential integral of the P109 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P109 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P109 : ℝ)
        * rotTrue2662 (phaseArg2658P109 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            Complex.exp (complexPanelPhase2649 u - complexPanelPhase2649 0))
      - embedPair2542 panelAssemblyCenter2662P109)
    ≤ (panelAssemblyCharge2662P109 : ℝ) + (panelResidualCharge2662P109 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2649
      ≤ complexPanelHalfWidthReal2649 := by
    have hn := complexPanelHalfWidthReal_nonneg2649
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2649)
      complexPanelHalfWidthReal2649, HasDerivAt complexPanelPhase2649
      (complexPanelPhaseDerivative2649 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2649 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2649 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2649 u - complexPanelPhase2649 0))
      (Icc (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2649 x
        - complexPanelPhase2649 0)
        (complexPanelPhaseDerivative2649 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2649 u
      - complexPanelPhase2649 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P109)
      (Icc (-complexPanelHalfWidthReal2649) complexPanelHalfWidthReal2649) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P109 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2649 u - complexPanelPhase2649 0)
      - complexPolyEval2647 complexPanelPolynomial2648P109 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2649)
        complexPanelHalfWidthReal2649 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P109)
      MeasureTheory.volume (-complexPanelHalfWidthReal2649)
        complexPanelHalfWidthReal2649 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P109 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P109 : ℝ)
      + (ampRadius2657P109 : ℝ) * (pairMagnitude2542 phaseValue2658P109 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P109 : ℝ)
      ≤ (panelAssemblyCharge2662P109 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P109 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P109])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P109 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P109])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P109 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P109 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P109 : ℝ) * (phaseRadius2658P109 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P109 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P109
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P109)
          * ((complexPanelResidualUpper2648P109 / deficitSq2662P109 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2649 ^ 2)))
      ≤ (panelResidualCharge2662P109 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2649 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2649, complexPanelHalfWidth2649]
    have hexpE : Real.exp (ampExpArg2662P109) ≤ (((3 : ℚ) ^ 1 : ℚ) : ℝ) := by
      unfold ampExpArg2662P109
      exact exp_le_three_pow_rat2662 (((1 / 5) : ℝ)) 1 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P109 / deficitSq2662P109 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P109 := by
          norm_num [complexPanelResidualUpper2648P109]
        have h2 : (0 : ℚ) < deficitSq2662P109 := by
          norm_num [deficitSq2662P109]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P109, ampRadius2657P109])
    calc ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P109)
            * ((complexPanelResidualUpper2648P109 / deficitSq2662P109 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2649 ^ 2)))
        = ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P109)
              * ((complexPanelResidualUpper2648P109 / deficitSq2662P109 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P109 + ampRadius2657P109 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 1 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P109 / deficitSq2662P109 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P109 : ℝ) := by
          unfold panelResidualCharge2662P109
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2649
    complexPanelPolynomial2648P109
    (ampArg2657P109 : ℝ) (phaseArg2658P109 : ℝ) ampExpArg2662P109
    complexPanelHalfWidthReal2649
    ampValue2657P109 ampRadius2657P109 phaseRadius2658P109
    complexPanelResidualUpper2648P109 deficitSq2662P109
    phaseValue2658P109 complexPanelIntegral2648P109
    (panelAssemblyCharge2662P109 : ℝ) (panelResidualCharge2662P109 : ℝ)
    ampPin2657P109 phaseCosPin2658P109 phaseSinPin2658P109
    (by norm_num [ampValue2657P109]) (by norm_num [ampRadius2657P109])
    (by norm_num [phaseRadius2658P109])
    hEint hPint complexPanelPolyIntegral2649
    (by
      have h := complexPanelIntegralError2649
      simpa [ampExpArg2662P109, deficitSq2662P109] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P109
      = (ampValue2657P109 : ℂ)
        * (embedPair2542 phaseValue2658P109
          * embedPair2542 complexPanelIntegral2648P109) := by
    simp only [panelAssemblyCenter2662P109, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P109. -/
theorem panelCenterNormalization2662P109 :
    (∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P109 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P109 : ℝ)
        * rotTrue2662 (phaseArg2658P109 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            Complex.exp (complexPanelPhase2649 u - complexPanelPhase2649 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P109 : ℝ) (complexPanelPsi2648P109 : ℝ)
    (complexPanelCenter2648P109 : ℝ) complexPanelHalfWidthReal2649
    panelBetaTie2662P109 complexPanelHalfWidthReal_nonneg2649
    (by
      norm_num [complexPanelCenter2648P109, complexPanelHalfWidthReal2649,
        complexPanelHalfWidth2649])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P109 : ℝ)
        (complexPanelPsi2648P109 : ℝ) (complexPanelCenter2648P109 : ℝ)
      = ampCenterComplex2662 (ampArg2657P109 : ℝ)
        * rotTrue2662 (phaseArg2658P109 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P109, phaseArgPin2662P109]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P109 : ℝ)
            (complexPanelPsi2648P109 : ℝ) (complexPanelCenter2648P109 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P109 : ℝ)
            (complexPanelPsi2648P109 : ℝ) (complexPanelCenter2648P109 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            Complex.exp (complexPanelPhase2649 u - complexPanelPhase2649 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P109 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2649)..complexPanelHalfWidthReal2649,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P109 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P109)
      ≤ (panelAssemblyCharge2662P109 : ℝ) + (panelResidualCharge2662P109 : ℝ) := by
  rw [panelCenterNormalization2662P109]
  exact panelValueBall2662P109

#print axioms capturedNodes2584_zero_eq2662P109
#print axioms capturedModulations2584_three_eq2662P109
#print axioms storedWidth_three_eq2662P109
#print axioms panelBetaTie2662P109
#print axioms ampArgPin2662P109
#print axioms phaseArgPin2662P109
#print axioms panelValueBall2662P109
#print axioms panelCenterNormalization2662P109
#print axioms panelTrueBall2662P109

end ConnesWeilRH.Dev
