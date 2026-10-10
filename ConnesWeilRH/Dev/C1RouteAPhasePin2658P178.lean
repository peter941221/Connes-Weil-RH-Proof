import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 178 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P178 : ℚ := (1007136972907748837219272229471593726719655957075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P178 : RatPair2542 := ((606819298229788310659861828333965152392015619112151063691067902297896634389679321326767093102209 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (878851804174888200975040501808907374027280594515321628493297826827324164302063166520836237125095 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P178 : ℚ := (1775700820616086909257915722149455985572530344361 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P178 :
    phaseExp2646 phaseArg2658P178 20 =
      ((phaseValue2658P178.1,
        phaseValue2658P178.2), phaseRadius2658P178) := by
  decide +kernel

theorem phaseCosPin2658P178 :
    |Real.cos (phaseArg2658P178 : ℝ) -
      (phaseValue2658P178.1 : ℝ)| ≤
        (phaseRadius2658P178 : ℝ) := by
  have hsmall : |((phaseArg2658P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P178]
  have h := phaseExp_cos_error2646 phaseArg2658P178 20 hsmall
  rw [phaseChain2658P178] at h
  simpa [phaseValue2658P178] using h

theorem phaseSinPin2658P178 :
    |Real.sin (phaseArg2658P178 : ℝ) -
      (phaseValue2658P178.2 : ℝ)| ≤
        (phaseRadius2658P178 : ℝ) := by
  have hsmall : |((phaseArg2658P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P178]
  have h := phaseExp_sin_error2646 phaseArg2658P178 20 hsmall
  rw [phaseChain2658P178] at h
  simpa [phaseValue2658P178] using h

end ConnesWeilRH.Dev
