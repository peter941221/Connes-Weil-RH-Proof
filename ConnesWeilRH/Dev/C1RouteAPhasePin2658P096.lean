import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 096 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P096 : ℚ := (18092280950438601866214471188112462156640526175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P096 : RatPair2542 := ((1066379402603225016187982101159062220165221388315823281328407796304021008598353196972188068567053 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (917112181364665515638932612598260583066533951371043337430478854450958686395295589891118513859 / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192))
def phaseRadius2658P096 : ℚ := (3696716152093718818503152586076645783873808077563 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P096 :
    phaseExp2646 phaseArg2658P096 20 =
      ((phaseValue2658P096.1,
        phaseValue2658P096.2), phaseRadius2658P096) := by
  decide +kernel

theorem phaseCosPin2658P096 :
    |Real.cos (phaseArg2658P096 : ℝ) -
      (phaseValue2658P096.1 : ℝ)| ≤
        (phaseRadius2658P096 : ℝ) := by
  have hsmall : |((phaseArg2658P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P096]
  have h := phaseExp_cos_error2646 phaseArg2658P096 20 hsmall
  rw [phaseChain2658P096] at h
  simpa [phaseValue2658P096] using h

theorem phaseSinPin2658P096 :
    |Real.sin (phaseArg2658P096 : ℝ) -
      (phaseValue2658P096.2 : ℝ)| ≤
        (phaseRadius2658P096 : ℝ) := by
  have hsmall : |((phaseArg2658P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P096]
  have h := phaseExp_sin_error2646 phaseArg2658P096 20 hsmall
  rw [phaseChain2658P096] at h
  simpa [phaseValue2658P096] using h

end ConnesWeilRH.Dev
