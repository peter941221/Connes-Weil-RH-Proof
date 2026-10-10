import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 102 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P102 : ℚ := (90461404752193009331072355940562310783202630875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P102 : RatPair2542 := ((1027884068134671987590691988136808741888489128075688495331749912164933188433005542195972687949855 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (72484695315832793282007112322238906359598924976983939423007479439187062207475326874846382318393 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P102 : ℚ := (1083526019846711628958373202874159810276393614565 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P102 :
    phaseExp2646 phaseArg2658P102 20 =
      ((phaseValue2658P102.1,
        phaseValue2658P102.2), phaseRadius2658P102) := by
  decide +kernel

theorem phaseCosPin2658P102 :
    |Real.cos (phaseArg2658P102 : ℝ) -
      (phaseValue2658P102.1 : ℝ)| ≤
        (phaseRadius2658P102 : ℝ) := by
  have hsmall : |((phaseArg2658P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P102]
  have h := phaseExp_cos_error2646 phaseArg2658P102 20 hsmall
  rw [phaseChain2658P102] at h
  simpa [phaseValue2658P102] using h

theorem phaseSinPin2658P102 :
    |Real.sin (phaseArg2658P102 : ℝ) -
      (phaseValue2658P102.2 : ℝ)| ≤
        (phaseRadius2658P102 : ℝ) := by
  have hsmall : |((phaseArg2658P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P102]
  have h := phaseExp_sin_error2646 phaseArg2658P102 20 hsmall
  rw [phaseChain2658P102] at h
  simpa [phaseValue2658P102] using h

end ConnesWeilRH.Dev
