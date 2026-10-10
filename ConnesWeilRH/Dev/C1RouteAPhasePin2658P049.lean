import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 049 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P049 : ℚ := (-548799188829970923275172292706078018751429293975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P049 : RatPair2542 := ((-1737548170428125713895174604125548846535780082507581353696623720977032557549652410363912193072199 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1242323216020721483901031029452054463808840951790644525716413414828109467242834164538881274871533 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P049 : ℚ := (16690380805527830628847198738564821111433372937025 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P049 :
    phaseExp2646 phaseArg2658P049 20 =
      ((phaseValue2658P049.1,
        phaseValue2658P049.2), phaseRadius2658P049) := by
  decide +kernel

theorem phaseCosPin2658P049 :
    |Real.cos (phaseArg2658P049 : ℝ) -
      (phaseValue2658P049.1 : ℝ)| ≤
        (phaseRadius2658P049 : ℝ) := by
  have hsmall : |((phaseArg2658P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P049]
  have h := phaseExp_cos_error2646 phaseArg2658P049 20 hsmall
  rw [phaseChain2658P049] at h
  simpa [phaseValue2658P049] using h

theorem phaseSinPin2658P049 :
    |Real.sin (phaseArg2658P049 : ℝ) -
      (phaseValue2658P049.2 : ℝ)| ≤
        (phaseRadius2658P049 : ℝ) := by
  have hsmall : |((phaseArg2658P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P049]
  have h := phaseExp_sin_error2646 phaseArg2658P049 20 hsmall
  rw [phaseChain2658P049] at h
  simpa [phaseValue2658P049] using h

end ConnesWeilRH.Dev
