import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 154 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P154 : ℚ := (717660477700731207359840690461794332213407538275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P154 : RatPair2542 := ((531990137918445734495135430968155719562770255398035506404236715061624365715523591162049724059665 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (46249667662592853265688609569736344439800594779335462346201542810405300069019795969829963370749 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P154 : ℚ := (7753076229140789814433981312632365787070549065219 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P154 :
    phaseExp2646 phaseArg2658P154 20 =
      ((phaseValue2658P154.1,
        phaseValue2658P154.2), phaseRadius2658P154) := by
  decide +kernel

theorem phaseCosPin2658P154 :
    |Real.cos (phaseArg2658P154 : ℝ) -
      (phaseValue2658P154.1 : ℝ)| ≤
        (phaseRadius2658P154 : ℝ) := by
  have hsmall : |((phaseArg2658P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P154]
  have h := phaseExp_cos_error2646 phaseArg2658P154 20 hsmall
  rw [phaseChain2658P154] at h
  simpa [phaseValue2658P154] using h

theorem phaseSinPin2658P154 :
    |Real.sin (phaseArg2658P154 : ℝ) -
      (phaseValue2658P154.2 : ℝ)| ≤
        (phaseRadius2658P154 : ℝ) := by
  have hsmall : |((phaseArg2658P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P154]
  have h := phaseExp_sin_error2646 phaseArg2658P154 20 hsmall
  rw [phaseChain2658P154] at h
  simpa [phaseValue2658P154] using h

end ConnesWeilRH.Dev
