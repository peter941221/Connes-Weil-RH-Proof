import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 107 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P107 : ℚ := (150769007920321682218453926567603851305337718125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P107 : RatPair2542 := ((-1776089392885307912313827215409704764281614127589022249534588306936133332469707140223115185661351 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1186569461136807435249749718333201967527689382854761568648991590613253119195052130344377159556029 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P107 : ℚ := (9835494876156038838979392841678327723118803709013 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P107 :
    phaseExp2646 phaseArg2658P107 20 =
      ((phaseValue2658P107.1,
        phaseValue2658P107.2), phaseRadius2658P107) := by
  decide +kernel

theorem phaseCosPin2658P107 :
    |Real.cos (phaseArg2658P107 : ℝ) -
      (phaseValue2658P107.1 : ℝ)| ≤
        (phaseRadius2658P107 : ℝ) := by
  have hsmall : |((phaseArg2658P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P107]
  have h := phaseExp_cos_error2646 phaseArg2658P107 20 hsmall
  rw [phaseChain2658P107] at h
  simpa [phaseValue2658P107] using h

theorem phaseSinPin2658P107 :
    |Real.sin (phaseArg2658P107 : ℝ) -
      (phaseValue2658P107.2 : ℝ)| ≤
        (phaseRadius2658P107 : ℝ) := by
  have hsmall : |((phaseArg2658P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P107]
  have h := phaseExp_sin_error2646 phaseArg2658P107 20 hsmall
  rw [phaseChain2658P107] at h
  simpa [phaseValue2658P107] using h

end ConnesWeilRH.Dev
