import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 157 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P157 : ℚ := (753845039601608411092269632838019256526688590625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P157 : RatPair2542 := ((2094802156448814990597036369285435222654492205892255691548297900695761420980433155864159493891741 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (208713046405579101824674660843284351680591085892153363673707603396118145585504153507532078704597 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P157 : ℚ := (1999157559947813255420704277950882257968649711897 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P157 :
    phaseExp2646 phaseArg2658P157 20 =
      ((phaseValue2658P157.1,
        phaseValue2658P157.2), phaseRadius2658P157) := by
  decide +kernel

theorem phaseCosPin2658P157 :
    |Real.cos (phaseArg2658P157 : ℝ) -
      (phaseValue2658P157.1 : ℝ)| ≤
        (phaseRadius2658P157 : ℝ) := by
  have hsmall : |((phaseArg2658P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P157]
  have h := phaseExp_cos_error2646 phaseArg2658P157 20 hsmall
  rw [phaseChain2658P157] at h
  simpa [phaseValue2658P157] using h

theorem phaseSinPin2658P157 :
    |Real.sin (phaseArg2658P157 : ℝ) -
      (phaseValue2658P157.2 : ℝ)| ≤
        (phaseRadius2658P157 : ℝ) := by
  have hsmall : |((phaseArg2658P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P157]
  have h := phaseExp_sin_error2646 phaseArg2658P157 20 hsmall
  rw [phaseChain2658P157] at h
  simpa [phaseValue2658P157] using h

end ConnesWeilRH.Dev
