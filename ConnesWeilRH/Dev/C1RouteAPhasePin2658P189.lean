import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 189 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P189 : ℚ := (1139813699877631917571511684851085115868353149025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P189 : RatPair2542 := ((-253231032169951523692840727775529287110528117690325265240009450582700817969091051794377209707657 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (-84629657901280546254944326806625938897929190286210007385661942394860627147018205558687792973227 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P189 : ℚ := (9911972813746497235337850630085523035777095070537 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P189 :
    phaseExp2646 phaseArg2658P189 20 =
      ((phaseValue2658P189.1,
        phaseValue2658P189.2), phaseRadius2658P189) := by
  decide +kernel

theorem phaseCosPin2658P189 :
    |Real.cos (phaseArg2658P189 : ℝ) -
      (phaseValue2658P189.1 : ℝ)| ≤
        (phaseRadius2658P189 : ℝ) := by
  have hsmall : |((phaseArg2658P189 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P189]
  have h := phaseExp_cos_error2646 phaseArg2658P189 20 hsmall
  rw [phaseChain2658P189] at h
  simpa [phaseValue2658P189] using h

theorem phaseSinPin2658P189 :
    |Real.sin (phaseArg2658P189 : ℝ) -
      (phaseValue2658P189.2 : ℝ)| ≤
        (phaseRadius2658P189 : ℝ) := by
  have hsmall : |((phaseArg2658P189 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P189]
  have h := phaseExp_sin_error2646 phaseArg2658P189 20 hsmall
  rw [phaseChain2658P189] at h
  simpa [phaseValue2658P189] using h

end ConnesWeilRH.Dev
