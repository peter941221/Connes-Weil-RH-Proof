import ConnesWeilRH.Dev.C1RouteAPanelComposition2662
import ConnesWeilRH.Dev.C1RouteAAmpPin2657P147
import ConnesWeilRH.Dev.C1RouteAPhasePin2658P147
import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2655P147
import ConnesWeilRH.Dev.C1RouteAComplexPanelAnalytic2656P147
import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P147 true panel ball for the actual (0,3) entry integrand (record 2662)

First instance of the generic record-2662 composition lemma, at the negative
center `-1/200` (the mirror shape class of the record-2661 P095 pilot), with
the record-2656 analytic exponential factor rationalized to `3^1`.  The
residual charge is a pure rational, so the 190-panel partition budget is a
rational sum:

  |integral of the actual normalized integrand over the P147 panel
    - assembly_center|_L1
    <= panelAssemblyCharge2662P147 + panelResidualCharge2662P147.

Scope: entry (0,3), panel P147 only.  No partition sum, no edge slices, no
entry containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open Set

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2662P147 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2662P147 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2662P147 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2662P147 :
    capturedNodes2584 0 = nodeEntry0_2662P147 := rfl

theorem capturedModulations2584_three_eq2662P147 :
    capturedModulations2584 3 = modulationEntry3_2662P147 := rfl

theorem storedWidth_three_eq2662P147 : storedWidth 3 = widthEntry3_2662P147 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 P147 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2662P147 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P147 : ℝ) : ℂ)
        + ((complexPanelPsi2648P147 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2662P147, capturedModulations2584_three_eq2662P147,
    storedWidth_three_eq2662P147]
  apply Complex.ext
  · simp only [nodeEntry0_2662P147, modulationEntry3_2662P147, widthEntry3_2662P147,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P147, complexPanelPsi2648P147]
  · simp only [nodeEntry0_2662P147, modulationEntry3_2662P147, widthEntry3_2662P147,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P147, complexPanelPsi2648P147]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2662P147 :
    (complexPanelBeta2648P147 : ℝ) * (complexPanelCenter2648P147 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P147 : ℝ) ^ 2)
      = (ampArg2657P147 : ℝ) := by
  norm_num [complexPanelBeta2648P147, complexPanelCenter2648P147, ampArg2657P147]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2662P147 :
    (complexPanelPsi2648P147 : ℝ) * (complexPanelCenter2648P147 : ℝ)
      = (phaseArg2658P147 : ℝ) := by
  norm_num [complexPanelPsi2648P147, complexPanelCenter2648P147, phaseArg2658P147]

/-- The record-2656 analytic exponential argument of panel P147. -/
noncomputable def ampExpArg2662P147 : ℝ := 2 * ((149111827 / 430920675) : ℝ)

/-- The record-2656 squared panel deficit of panel P147. -/
def deficitSq2662P147 : ℚ := ((7191 / 10000 : ℚ) ^ 2)

/-- Rationalized residual charge: the record-2656 exponential factor is
bounded by `3^1`. -/
def panelResidualCharge2662P147 : ℚ :=
  (ampValue2657P147 + ampRadius2657P147)
    * (2 * ((3 : ℚ) ^ 1 * (complexPanelResidualUpper2648P147 / deficitSq2662P147))
      * (2 * ((1 / 200 : ℚ) ^ 2)))

/-- Exact rational assembly center (panel P147). -/
def panelAssemblyCenter2662P147 : RatPair2542 :=
  pairScale2542 ampValue2657P147
    (pairMul2542 phaseValue2658P147 complexPanelIntegral2648P147)

/-- Exact rational assembly charge (panel P147). -/
def panelAssemblyCharge2662P147 : ℚ :=
  ampRadius2657P147 * (pairMagnitude2542 phaseValue2658P147
      + 2 * phaseRadius2658P147)
      * pairMagnitude2542 complexPanelIntegral2648P147
    + (ampValue2657P147 + ampRadius2657P147) * (2 * phaseRadius2658P147)
      * pairMagnitude2542 complexPanelIntegral2648P147

/-- The true panel exponential integral of the P147 table phase lies in the
record-2662 L1 ball around the exact rational assembly center. -/
theorem panelValueBall2662P147 :
    complexL12660 (ampCenterComplex2662 (ampArg2657P147 : ℝ)
        * rotTrue2662 (phaseArg2658P147 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
            Complex.exp (complexPanelPhase2656P147 u - complexPanelPhase2656P147 0))
      - embedPair2542 panelAssemblyCenter2662P147)
    ≤ (panelAssemblyCharge2662P147 : ℝ) + (panelResidualCharge2662P147 : ℝ) := by
  have horder : -complexPanelHalfWidthReal2656P147
      ≤ complexPanelHalfWidthReal2656P147 := by
    have hn := complexPanelHalfWidthReal_nonneg2656P147
    linarith
  have hphaseDeriv : ∀ u ∈ Icc (-complexPanelHalfWidthReal2656P147)
      complexPanelHalfWidthReal2656P147, HasDerivAt complexPanelPhase2656P147
      (complexPanelPhaseDerivative2656P147 u) u := by
    intro u hu
    refine complexPanelPhase_hasDerivAt2656P147 u (ne_of_gt ?_)
    have hlow := complexPanelDeficit_lower2656P147 u hu
    linarith
  have hEcontE : ContinuousOn (fun u => Complex.exp
      (complexPanelPhase2656P147 u - complexPanelPhase2656P147 0))
      (Icc (-complexPanelHalfWidthReal2656P147) complexPanelHalfWidthReal2656P147) := by
    intro u hu
    have hdPi : HasDerivAt (fun x => complexPanelPhase2656P147 x
        - complexPanelPhase2656P147 0)
        (complexPanelPhaseDerivative2656P147 u) u := (hphaseDeriv u hu).sub_const _
    exact (Complex.hasDerivAt_exp (complexPanelPhase2656P147 u
      - complexPanelPhase2656P147 0)).comp u hdPi
      |>.continuousAt.continuousWithinAt
  have hPcont : ContinuousOn (complexPolyEval2647 complexPanelPolynomial2648P147)
      (Icc (-complexPanelHalfWidthReal2656P147) complexPanelHalfWidthReal2656P147) :=
    HasDerivAt.continuousOn fun u _ =>
      complexPolyEval2647_hasDerivAt complexPanelPolynomial2648P147 u
  have hEint : IntervalIntegrable (fun u => Complex.exp
      (complexPanelPhase2656P147 u - complexPanelPhase2656P147 0)
      - complexPolyEval2647 complexPanelPolynomial2648P147 u)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P147)
        complexPanelHalfWidthReal2656P147 :=
    (hEcontE.sub hPcont).intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hPint : IntervalIntegrable (complexPolyEval2647 complexPanelPolynomial2648P147)
      MeasureTheory.volume (-complexPanelHalfWidthReal2656P147)
        complexPanelHalfWidthReal2656P147 :=
    hPcont.intervalIntegrable_of_Icc horder (μ := MeasureTheory.volume)
  have hac : ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ) * (2 : ℝ)
        * (phaseRadius2658P147 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P147 : ℝ)
      + (ampRadius2657P147 : ℝ) * (pairMagnitude2542 phaseValue2658P147 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P147 : ℝ)
      ≤ (panelAssemblyCharge2662P147 : ℝ) := by
    have hR1 : (0 : ℝ) ≤ (ampRadius2657P147 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampRadius2657P147])
    have hR2 : (0 : ℝ) ≤ (phaseRadius2658P147 : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [phaseRadius2658P147])
    have hR3 : (0 : ℝ) ≤ (pairMagnitude2542 phaseValue2658P147 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hR4 : (0 : ℝ) ≤ (pairMagnitude2542 complexPanelIntegral2648P147 : ℝ) :=
      Rat.cast_nonneg.2 (by unfold pairMagnitude2542; positivity)
    have hthree : (0 : ℝ) ≤ (ampRadius2657P147 : ℝ) * (phaseRadius2658P147 : ℝ)
        * (pairMagnitude2542 complexPanelIntegral2648P147 : ℝ) :=
      mul_nonneg (mul_nonneg hR1 hR2) hR4
    unfold panelAssemblyCharge2662P147
    push_cast
    nlinarith [hR1, hR2, hR3, hR4, hthree]
  have hres : ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ)
      * (2 * (Real.exp (ampExpArg2662P147)
          * ((complexPanelResidualUpper2648P147 / deficitSq2662P147 : ℚ) : ℝ)
          * (2 * complexPanelHalfWidthReal2656P147 ^ 2)))
      ≤ (panelResidualCharge2662P147 : ℝ) := by
    have hhw : complexPanelHalfWidthReal2656P147 = ((1 / 200 : ℚ) : ℝ) := by
      norm_num [complexPanelHalfWidthReal2656P147, complexPanelHalfWidth2656P147]
    have hexpE : Real.exp (ampExpArg2662P147) ≤ (((3 : ℚ) ^ 1 : ℚ) : ℝ) := by
      unfold ampExpArg2662P147
      exact exp_le_three_pow_rat2662 (2 * ((149111827 / 430920675) : ℝ)) 1 (by norm_num)
    have hCnn : (0 : ℝ)
        ≤ ((complexPanelResidualUpper2648P147 / deficitSq2662P147 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by
        have h1 : (0 : ℚ) < complexPanelResidualUpper2648P147 := by
          norm_num [complexPanelResidualUpper2648P147]
        have h2 : (0 : ℚ) < deficitSq2662P147 := by
          norm_num [deficitSq2662P147]
        exact (div_pos h1 h2).le)
    have h0 : (0 : ℝ) ≤ ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ) :=
      Rat.cast_nonneg.2 (by norm_num [ampValue2657P147, ampRadius2657P147])
    calc ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ)
        * (2 * (Real.exp (ampExpArg2662P147)
            * ((complexPanelResidualUpper2648P147 / deficitSq2662P147 : ℚ) : ℝ)
            * (2 * complexPanelHalfWidthReal2656P147 ^ 2)))
        = ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ)
          * (2 * (Real.exp (ampExpArg2662P147)
              * ((complexPanelResidualUpper2648P147 / deficitSq2662P147 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by rw [hhw]
      _ ≤ ((ampValue2657P147 + ampRadius2657P147 : ℚ) : ℝ)
          * (2 * ((((3 : ℚ) ^ 1 : ℚ) : ℝ)
              * ((complexPanelResidualUpper2648P147 / deficitSq2662P147 : ℚ) : ℝ)
              * (2 * ((1 / 200 : ℚ) : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ h0
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexpE hCnn)
            (by positivity)
      _ = (panelResidualCharge2662P147 : ℝ) := by
          unfold panelResidualCharge2662P147
          push_cast
          ring
  have hball := panelL1Ball2662 complexPanelPhase2656P147
    complexPanelPolynomial2648P147
    (ampArg2657P147 : ℝ) (phaseArg2658P147 : ℝ) ampExpArg2662P147
    complexPanelHalfWidthReal2656P147
    ampValue2657P147 ampRadius2657P147 phaseRadius2658P147
    complexPanelResidualUpper2648P147 deficitSq2662P147
    phaseValue2658P147 complexPanelIntegral2648P147
    (panelAssemblyCharge2662P147 : ℝ) (panelResidualCharge2662P147 : ℝ)
    ampPin2657P147 phaseCosPin2658P147 phaseSinPin2658P147
    (by norm_num [ampValue2657P147]) (by norm_num [ampRadius2657P147])
    (by norm_num [phaseRadius2658P147])
    hEint hPint complexPanelPolyIntegral2656P147
    (by
      have h := complexPanelIntegralError2656P147
      simpa [ampExpArg2662P147, deficitSq2662P147] using h)
    hac hres
  have hcenter : embedPair2542 panelAssemblyCenter2662P147
      = (ampValue2657P147 : ℂ)
        * (embedPair2542 phaseValue2658P147
          * embedPair2542 complexPanelIntegral2648P147) := by
    simp only [panelAssemblyCenter2662P147, embedPair_scale2542, embedPair_mul2542]
  rw [hcenter]
  exact hball

/-- Center normalization for the actual (0,3) entry integrand on panel P147. -/
theorem panelCenterNormalization2662P147 :
    (∫ position in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P147 : ℝ) + position))
      = ampCenterComplex2662 (ampArg2657P147 : ℝ)
        * rotTrue2662 (phaseArg2658P147 : ℝ)
        * (∫ u in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
            Complex.exp (complexPanelPhase2656P147 u - complexPanelPhase2656P147 0)) := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P147 : ℝ) (complexPanelPsi2648P147 : ℝ)
    (complexPanelCenter2648P147 : ℝ) complexPanelHalfWidthReal2656P147
    panelBetaTie2662P147 complexPanelHalfWidthReal_nonneg2656P147
    (by
      norm_num [complexPanelCenter2648P147, complexPanelHalfWidthReal2656P147,
        complexPanelHalfWidth2656P147])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P147 : ℝ)
        (complexPanelPsi2648P147 : ℝ) (complexPanelCenter2648P147 : ℝ)
      = ampCenterComplex2662 (ampArg2657P147 : ℝ)
        * rotTrue2662 (phaseArg2658P147 : ℝ) := by
    unfold panelCenterFactor2661 ampCenterComplex2662 rotTrue2662
    rw [ampArgPin2662P147, phaseArgPin2662P147]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P147 : ℝ)
            (complexPanelPsi2648P147 : ℝ) (complexPanelCenter2648P147 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P147 : ℝ)
            (complexPanelPsi2648P147 : ℝ) (complexPanelCenter2648P147 : ℝ) 0))
        = (∫ u in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
            Complex.exp (complexPanelPhase2656P147 u - complexPanelPhase2656P147 0)) := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2662 rational L1 ball. -/
theorem panelTrueBall2662P147 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P147)..complexPanelHalfWidthReal2656P147,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P147 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2662P147)
      ≤ (panelAssemblyCharge2662P147 : ℝ) + (panelResidualCharge2662P147 : ℝ) := by
  rw [panelCenterNormalization2662P147]
  exact panelValueBall2662P147

#print axioms capturedNodes2584_zero_eq2662P147
#print axioms capturedModulations2584_three_eq2662P147
#print axioms storedWidth_three_eq2662P147
#print axioms panelBetaTie2662P147
#print axioms ampArgPin2662P147
#print axioms phaseArgPin2662P147
#print axioms panelValueBall2662P147
#print axioms panelCenterNormalization2662P147
#print axioms panelTrueBall2662P147

end ConnesWeilRH.Dev
