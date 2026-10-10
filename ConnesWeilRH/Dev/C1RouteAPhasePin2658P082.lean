import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 082 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P082 : ℚ := (-150769007920321682218453926567603851305337718125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P082 : RatPair2542 := ((-888044696442653956156913607704852382140807063794511124767294153468066666234853570111557593414575 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-1186569461136807435249749718333201967527689382854761568648991590613253119195052130344377157816027 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P082 : ℚ := (9835494876156038838979392841678327723118803709013 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P082 :
    phaseExp2646 phaseArg2658P082 20 =
      ((phaseValue2658P082.1,
        phaseValue2658P082.2), phaseRadius2658P082) := by
  decide +kernel

theorem phaseCosPin2658P082 :
    |Real.cos (phaseArg2658P082 : ℝ) -
      (phaseValue2658P082.1 : ℝ)| ≤
        (phaseRadius2658P082 : ℝ) := by
  have hsmall : |((phaseArg2658P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P082]
  have h := phaseExp_cos_error2646 phaseArg2658P082 20 hsmall
  rw [phaseChain2658P082] at h
  simpa [phaseValue2658P082] using h

theorem phaseSinPin2658P082 :
    |Real.sin (phaseArg2658P082 : ℝ) -
      (phaseValue2658P082.2 : ℝ)| ≤
        (phaseRadius2658P082 : ℝ) := by
  have hsmall : |((phaseArg2658P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P082]
  have h := phaseExp_sin_error2646 phaseArg2658P082 20 hsmall
  rw [phaseChain2658P082] at h
  simpa [phaseValue2658P082] using h

end ConnesWeilRH.Dev
