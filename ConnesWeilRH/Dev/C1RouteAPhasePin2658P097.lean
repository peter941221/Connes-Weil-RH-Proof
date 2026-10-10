import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 097 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P097 : ℚ := (30153801584064336443690785313520770261067543625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P097 : RatPair2542 := ((-447112631706933861623651750040244514161039072559140220239883650447526857093420246628470103385087 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-484948566595893890145325631267133859181169192970245918828170262154244248007062136784441401938013 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P097 : ℚ := (231401614889686422375015518194383087315638036085 / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584)

theorem phaseChain2658P097 :
    phaseExp2646 phaseArg2658P097 20 =
      ((phaseValue2658P097.1,
        phaseValue2658P097.2), phaseRadius2658P097) := by
  decide +kernel

theorem phaseCosPin2658P097 :
    |Real.cos (phaseArg2658P097 : ℝ) -
      (phaseValue2658P097.1 : ℝ)| ≤
        (phaseRadius2658P097 : ℝ) := by
  have hsmall : |((phaseArg2658P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P097]
  have h := phaseExp_cos_error2646 phaseArg2658P097 20 hsmall
  rw [phaseChain2658P097] at h
  simpa [phaseValue2658P097] using h

theorem phaseSinPin2658P097 :
    |Real.sin (phaseArg2658P097 : ℝ) -
      (phaseValue2658P097.2 : ℝ)| ≤
        (phaseRadius2658P097 : ℝ) := by
  have hsmall : |((phaseArg2658P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P097]
  have h := phaseExp_sin_error2646 phaseArg2658P097 20 hsmall
  rw [phaseChain2658P097] at h
  simpa [phaseValue2658P097] using h

end ConnesWeilRH.Dev
