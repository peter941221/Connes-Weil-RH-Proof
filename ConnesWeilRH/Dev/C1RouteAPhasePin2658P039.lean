import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 039 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P039 : ℚ := (-669414395166228269049935433960161099795699468475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P039 : RatPair2542 := ((-955320168416284045517118068934996890519432307964445444289438357970898132651003332407386554604391 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-477611504876039255065143974704509626494932642574088507883688838877812738937276909692893331538881 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P039 : ℚ := (30171830713067272797648946464865717868237294616837 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P039 :
    phaseExp2646 phaseArg2658P039 20 =
      ((phaseValue2658P039.1,
        phaseValue2658P039.2), phaseRadius2658P039) := by
  decide +kernel

theorem phaseCosPin2658P039 :
    |Real.cos (phaseArg2658P039 : ℝ) -
      (phaseValue2658P039.1 : ℝ)| ≤
        (phaseRadius2658P039 : ℝ) := by
  have hsmall : |((phaseArg2658P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P039]
  have h := phaseExp_cos_error2646 phaseArg2658P039 20 hsmall
  rw [phaseChain2658P039] at h
  simpa [phaseValue2658P039] using h

theorem phaseSinPin2658P039 :
    |Real.sin (phaseArg2658P039 : ℝ) -
      (phaseValue2658P039.2 : ℝ)| ≤
        (phaseRadius2658P039 : ℝ) := by
  have hsmall : |((phaseArg2658P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P039]
  have h := phaseExp_sin_error2646 phaseArg2658P039 20 hsmall
  rw [phaseChain2658P039] at h
  simpa [phaseValue2658P039] using h

end ConnesWeilRH.Dev
