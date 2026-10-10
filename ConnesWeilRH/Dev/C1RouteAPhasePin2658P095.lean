import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 095 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P095 : ℚ := (6030760316812867288738157062704154052213508725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P095 : RatPair2542 := ((-1101716993493536092353788103546713840371692572268188122505680550340161294395672746913281879190663 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1829934502617445860312650386224014447522241277493428879303863532469575134886384122155523535765839 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P095 : ℚ := (985736475758277450365379109453678929593420614233 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P095 :
    phaseExp2646 phaseArg2658P095 20 =
      ((phaseValue2658P095.1,
        phaseValue2658P095.2), phaseRadius2658P095) := by
  decide +kernel

theorem phaseCosPin2658P095 :
    |Real.cos (phaseArg2658P095 : ℝ) -
      (phaseValue2658P095.1 : ℝ)| ≤
        (phaseRadius2658P095 : ℝ) := by
  have hsmall : |((phaseArg2658P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P095]
  have h := phaseExp_cos_error2646 phaseArg2658P095 20 hsmall
  rw [phaseChain2658P095] at h
  simpa [phaseValue2658P095] using h

theorem phaseSinPin2658P095 :
    |Real.sin (phaseArg2658P095 : ℝ) -
      (phaseValue2658P095.2 : ℝ)| ≤
        (phaseRadius2658P095 : ℝ) := by
  have hsmall : |((phaseArg2658P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P095]
  have h := phaseExp_sin_error2646 phaseArg2658P095 20 hsmall
  rw [phaseChain2658P095] at h
  simpa [phaseValue2658P095] using h

end ConnesWeilRH.Dev
