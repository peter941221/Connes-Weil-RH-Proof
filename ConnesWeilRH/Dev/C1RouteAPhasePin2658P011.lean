import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 011 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P011 : ℚ := (-1007136972907748837219272229471593726719655957075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P011 : RatPair2542 := ((75852412278723538832482728541745644049001952389018882961383487787237079298709915165845886530619 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-878851804174888200975040501808907374027280594515321628493297826827324164302063166520836237728079 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P011 : ℚ := (1775700820616086909257915722149455985572530344361 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P011 :
    phaseExp2646 phaseArg2658P011 20 =
      ((phaseValue2658P011.1,
        phaseValue2658P011.2), phaseRadius2658P011) := by
  decide +kernel

theorem phaseCosPin2658P011 :
    |Real.cos (phaseArg2658P011 : ℝ) -
      (phaseValue2658P011.1 : ℝ)| ≤
        (phaseRadius2658P011 : ℝ) := by
  have hsmall : |((phaseArg2658P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P011]
  have h := phaseExp_cos_error2646 phaseArg2658P011 20 hsmall
  rw [phaseChain2658P011] at h
  simpa [phaseValue2658P011] using h

theorem phaseSinPin2658P011 :
    |Real.sin (phaseArg2658P011 : ℝ) -
      (phaseValue2658P011.2 : ℝ)| ≤
        (phaseRadius2658P011 : ℝ) := by
  have hsmall : |((phaseArg2658P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P011]
  have h := phaseExp_sin_error2646 phaseArg2658P011 20 hsmall
  rw [phaseChain2658P011] at h
  simpa [phaseValue2658P011] using h

end ConnesWeilRH.Dev
