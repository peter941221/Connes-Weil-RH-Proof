import ConnesWeilRH.Dev.C1RouteAPanelCenterNormalization2661
import ConnesWeilRH.Dev.C1RouteAPanelBall2660P095
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584

/-!
# P095 center normalization against the actual entry integrand (record 2661)

Bridges the record-2655/2656 panel certificate spelling of the (0,3) entry
panel P095 to the actual normalized entry integrand
(`normalizedMomentIntegrand2618` at the captured parameters), and composes
with the record-2660 ball:

  integral of the actual normalized integrand over the P095 panel
    = (ampCenterComplex2660 * rotTrue2660P095) * panelIntegralTrue2660P095,

so the true panel integral of the ACTUAL entry integrand lies in the L1 ball
around `panelAssemblyCenter2659P095` with the record-2659/2660 charges.

Scope: entry (0,3), panel P095 only.  No 190-panel partition sum, no entry
containment, no producer GO.
-/

-- The long integral binders exceed the 100-character style limit by construction.
set_option linter.style.longLine false

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-- Captured node 0 as a literal complex number. -/
noncomputable def nodeEntry0_2661 : ℂ :=
  ⟨((4255901647865119 : ℝ) / 4503599627370496),
    ((5524291025718029 : ℝ) / 140737488355328)⟩

/-- Captured modulation 3 as a literal. -/
noncomputable def modulationEntry3_2661 : ℝ :=
  (5524291025718029 : ℝ) / 140737488355328

/-- Captured width 3 as a literal. -/
noncomputable def widthEntry3_2661 : ℝ :=
  (5224175567749775 : ℝ) / 2251799813685248

theorem capturedNodes2584_zero_eq2661 :
    capturedNodes2584 0 = nodeEntry0_2661 := rfl

theorem capturedModulations2584_three_eq2661 :
    capturedModulations2584 3 = modulationEntry3_2661 := rfl

theorem storedWidth_three_eq2661 : storedWidth 3 = widthEntry3_2661 := by
  rw [storedWidth_eq_capturedWidth2584]
  rfl

/-- Exact-rational tie: the captured (0,3) complex coefficient equals the
record-2655 panel-table coefficient `beta + i*psi`. -/
theorem panelBetaTie2661P095 :
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I)
        * ((storedWidth 3 ^ 2 : ℝ) : ℂ)
      = ((complexPanelBeta2648P095 : ℝ) : ℂ)
        + ((complexPanelPsi2648P095 : ℝ) : ℂ) * Complex.I := by
  rw [capturedNodes2584_zero_eq2661, capturedModulations2584_three_eq2661,
    storedWidth_three_eq2661]
  apply Complex.ext
  · simp only [nodeEntry0_2661, modulationEntry3_2661, widthEntry3_2661,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    norm_num [complexPanelBeta2648P095, complexPanelPsi2648P095]
  · simp only [nodeEntry0_2661, modulationEntry3_2661, widthEntry3_2661,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    norm_num [complexPanelBeta2648P095, complexPanelPsi2648P095]

/-- The record-2657 amplitude pin is the center-value exponent of the panel
table coefficient at the panel center. -/
theorem ampArgPin2661P095 :
    (complexPanelBeta2648P095 : ℝ) * (complexPanelCenter2648P095 : ℝ)
        - 30 / (1 - (complexPanelCenter2648P095 : ℝ) ^ 2)
      = (ampArg2657P095 : ℝ) := by
  norm_num [complexPanelBeta2648P095, complexPanelCenter2648P095, ampArg2657P095]

/-- The record-2658 rotation pin is `psi` times the panel center. -/
theorem phaseArgPin2661P095 :
    (complexPanelPsi2648P095 : ℝ) * (complexPanelCenter2648P095 : ℝ)
      = (phaseArg2658P095 : ℝ) := by
  norm_num [complexPanelPsi2648P095, complexPanelCenter2648P095, phaseArg2658P095]

/-- Center normalization for the actual (0,3) entry integrand on panel P095. -/
theorem panelCenterNormalization2661P095 :
    (∫ position in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
        normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
          (capturedNodes2584 0) ((complexPanelCenter2648P095 : ℝ) + position))
      = (ampCenterComplex2660 * rotTrue2660P095) * panelIntegralTrue2660P095 := by
  have hgen := panelCenterNormalization2661 (capturedModulations2584 3) (storedWidth 3 ^ 2)
    (capturedNodes2584 0) (complexPanelBeta2648P095 : ℝ) (complexPanelPsi2648P095 : ℝ)
    (complexPanelCenter2648P095 : ℝ) complexPanelHalfWidthReal2656P095
    panelBetaTie2661P095 complexPanelHalfWidthReal_nonneg2656P095
    (by
      norm_num [complexPanelCenter2648P095, complexPanelHalfWidthReal2656P095,
        complexPanelHalfWidth2656P095])
  rw [hgen]
  have hcf : panelCenterFactor2661 (complexPanelBeta2648P095 : ℝ)
        (complexPanelPsi2648P095 : ℝ) (complexPanelCenter2648P095 : ℝ)
      = ampCenterComplex2660 * rotTrue2660P095 := by
    unfold panelCenterFactor2661 ampCenterComplex2660 rotTrue2660P095
    rw [ampArgPin2661P095, phaseArgPin2661P095]
  rw [hcf]
  have hInt :
      (∫ position in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
        Complex.exp (panelPhase2661 (complexPanelBeta2648P095 : ℝ)
            (complexPanelPsi2648P095 : ℝ) (complexPanelCenter2648P095 : ℝ) position
          - panelPhase2661 (complexPanelBeta2648P095 : ℝ)
            (complexPanelPsi2648P095 : ℝ) (complexPanelCenter2648P095 : ℝ) 0))
        = panelIntegralTrue2660P095 := rfl
  rw [hInt]

/-- The true panel integral of the ACTUAL (0,3) entry integrand lies in the
record-2660 L1 ball. -/
theorem panelTrueBall2661P095 :
    complexL12660
        ((∫ position in (-complexPanelHalfWidthReal2656P095)..complexPanelHalfWidthReal2656P095,
            normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2)
              (capturedNodes2584 0) ((complexPanelCenter2648P095 : ℝ) + position))
          - embedPair2542 panelAssemblyCenter2659P095)
      ≤ (panelAssemblyCharge2659P095 : ℝ) + panelResidualCharge2660P095 := by
  rw [panelCenterNormalization2661P095]
  exact panelValueBall2660P095

#print axioms capturedNodes2584_zero_eq2661
#print axioms capturedModulations2584_three_eq2661
#print axioms storedWidth_three_eq2661
#print axioms panelBetaTie2661P095
#print axioms ampArgPin2661P095
#print axioms phaseArgPin2661P095
#print axioms panelCenterNormalization2661P095
#print axioms panelTrueBall2661P095

end ConnesWeilRH.Dev
