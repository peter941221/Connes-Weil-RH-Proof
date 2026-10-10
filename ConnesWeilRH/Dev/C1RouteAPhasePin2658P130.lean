import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 130 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P130 : ℚ := (428183982493713577500409151451994937707159119475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P130 : RatPair2542 := ((1498757385811984043796763752149362832088519514677763509057212432430008462283969140071361990080451 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-380473957395265000538934436404367913609321376419639884945192678077528975262319087534210433668381 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P130 : ℚ := (10235762545351001302830551402781349270128703413191 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P130 :
    phaseExp2646 phaseArg2658P130 20 =
      ((phaseValue2658P130.1,
        phaseValue2658P130.2), phaseRadius2658P130) := by
  decide +kernel

theorem phaseCosPin2658P130 :
    |Real.cos (phaseArg2658P130 : ℝ) -
      (phaseValue2658P130.1 : ℝ)| ≤
        (phaseRadius2658P130 : ℝ) := by
  have hsmall : |((phaseArg2658P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P130]
  have h := phaseExp_cos_error2646 phaseArg2658P130 20 hsmall
  rw [phaseChain2658P130] at h
  simpa [phaseValue2658P130] using h

theorem phaseSinPin2658P130 :
    |Real.sin (phaseArg2658P130 : ℝ) -
      (phaseValue2658P130.2 : ℝ)| ≤
        (phaseRadius2658P130 : ℝ) := by
  have hsmall : |((phaseArg2658P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P130]
  have h := phaseExp_sin_error2646 phaseArg2658P130 20 hsmall
  rw [phaseChain2658P130] at h
  simpa [phaseValue2658P130] using h

end ConnesWeilRH.Dev
