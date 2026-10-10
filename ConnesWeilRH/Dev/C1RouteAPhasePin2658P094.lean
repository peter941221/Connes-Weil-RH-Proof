import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 094 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P094 : ℚ := (-6030760316812867288738157062704154052213508725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P094 : RatPair2542 := ((-68857312093346005772111756471669615023230785766761757656605034396260080899729546682080117561785 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-1829934502617445860312650386224014447522241277493428879303863532469575134886384122155523534686149 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P094 : ℚ := (985736475758277450365379109453678929593420614233 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P094 :
    phaseExp2646 phaseArg2658P094 20 =
      ((phaseValue2658P094.1,
        phaseValue2658P094.2), phaseRadius2658P094) := by
  decide +kernel

theorem phaseCosPin2658P094 :
    |Real.cos (phaseArg2658P094 : ℝ) -
      (phaseValue2658P094.1 : ℝ)| ≤
        (phaseRadius2658P094 : ℝ) := by
  have hsmall : |((phaseArg2658P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P094]
  have h := phaseExp_cos_error2646 phaseArg2658P094 20 hsmall
  rw [phaseChain2658P094] at h
  simpa [phaseValue2658P094] using h

theorem phaseSinPin2658P094 :
    |Real.sin (phaseArg2658P094 : ℝ) -
      (phaseValue2658P094.2 : ℝ)| ≤
        (phaseRadius2658P094 : ℝ) := by
  have hsmall : |((phaseArg2658P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P094]
  have h := phaseExp_sin_error2646 phaseArg2658P094 20 hsmall
  rw [phaseChain2658P094] at h
  simpa [phaseValue2658P094] using h

end ConnesWeilRH.Dev
