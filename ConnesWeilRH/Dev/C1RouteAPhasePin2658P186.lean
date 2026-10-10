import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 186 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P186 : ℚ := (1103629137976754713839082742474860191555072096675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P186 : RatPair2542 := ((-1043957838433358703497596064261531778815522842315845523212011480984448570494279368231666152620661 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-450609302962547057571403952644359651245827170528227278193834438925749046285346280443073053477505 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P186 : ℚ := (2333379102527036670007225021082522755332082550363 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P186 :
    phaseExp2646 phaseArg2658P186 20 =
      ((phaseValue2658P186.1,
        phaseValue2658P186.2), phaseRadius2658P186) := by
  decide +kernel

theorem phaseCosPin2658P186 :
    |Real.cos (phaseArg2658P186 : ℝ) -
      (phaseValue2658P186.1 : ℝ)| ≤
        (phaseRadius2658P186 : ℝ) := by
  have hsmall : |((phaseArg2658P186 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P186]
  have h := phaseExp_cos_error2646 phaseArg2658P186 20 hsmall
  rw [phaseChain2658P186] at h
  simpa [phaseValue2658P186] using h

theorem phaseSinPin2658P186 :
    |Real.sin (phaseArg2658P186 : ℝ) -
      (phaseValue2658P186.2 : ℝ)| ≤
        (phaseRadius2658P186 : ℝ) := by
  have hsmall : |((phaseArg2658P186 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P186]
  have h := phaseExp_sin_error2646 phaseArg2658P186 20 hsmall
  rw [phaseChain2658P186] at h
  simpa [phaseValue2658P186] using h

end ConnesWeilRH.Dev
