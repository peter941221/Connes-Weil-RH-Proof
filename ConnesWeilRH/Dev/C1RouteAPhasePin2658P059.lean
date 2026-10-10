import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 059 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P059 : ℚ := (-428183982493713577500409151451994937707159119475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P059 : RatPair2542 := ((1498757385811984043796763752149362832088519514677763509057212432430008462283969140071361991559967 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (760947914790530001077868872808735827218642752839279769890385356155057950524638175068420866596231 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P059 : ℚ := (10235762545351001302830551402781349270128703413191 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P059 :
    phaseExp2646 phaseArg2658P059 20 =
      ((phaseValue2658P059.1,
        phaseValue2658P059.2), phaseRadius2658P059) := by
  decide +kernel

theorem phaseCosPin2658P059 :
    |Real.cos (phaseArg2658P059 : ℝ) -
      (phaseValue2658P059.1 : ℝ)| ≤
        (phaseRadius2658P059 : ℝ) := by
  have hsmall : |((phaseArg2658P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P059]
  have h := phaseExp_cos_error2646 phaseArg2658P059 20 hsmall
  rw [phaseChain2658P059] at h
  simpa [phaseValue2658P059] using h

theorem phaseSinPin2658P059 :
    |Real.sin (phaseArg2658P059 : ℝ) -
      (phaseValue2658P059.2 : ℝ)| ≤
        (phaseRadius2658P059 : ℝ) := by
  have hsmall : |((phaseArg2658P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P059]
  have h := phaseExp_sin_error2646 phaseArg2658P059 20 hsmall
  rw [phaseChain2658P059] at h
  simpa [phaseValue2658P059] using h

end ConnesWeilRH.Dev
