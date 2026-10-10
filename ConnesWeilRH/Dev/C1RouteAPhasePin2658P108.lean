import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 108 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P108 : ℚ := (162830528553947416795930240693012159409764735575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P108 : RatPair2542 := ((1879728942109355008409367786792957058151651419073854914098631729684239177543722735227505635738539 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1014425808927710743558429774594186135921222639096775184018776441213393510441645236737909290150973 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P108 : ℚ := (11227014341152089288072818821579668991431060944245 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P108 :
    phaseExp2646 phaseArg2658P108 20 =
      ((phaseValue2658P108.1,
        phaseValue2658P108.2), phaseRadius2658P108) := by
  decide +kernel

theorem phaseCosPin2658P108 :
    |Real.cos (phaseArg2658P108 : ℝ) -
      (phaseValue2658P108.1 : ℝ)| ≤
        (phaseRadius2658P108 : ℝ) := by
  have hsmall : |((phaseArg2658P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P108]
  have h := phaseExp_cos_error2646 phaseArg2658P108 20 hsmall
  rw [phaseChain2658P108] at h
  simpa [phaseValue2658P108] using h

theorem phaseSinPin2658P108 :
    |Real.sin (phaseArg2658P108 : ℝ) -
      (phaseValue2658P108.2 : ℝ)| ≤
        (phaseRadius2658P108 : ℝ) := by
  have hsmall : |((phaseArg2658P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P108]
  have h := phaseExp_sin_error2646 phaseArg2658P108 20 hsmall
  rw [phaseChain2658P108] at h
  simpa [phaseValue2658P108] using h

end ConnesWeilRH.Dev
