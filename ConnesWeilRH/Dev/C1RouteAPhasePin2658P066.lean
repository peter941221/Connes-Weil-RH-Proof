import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 066 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P066 : ℚ := (-343753338058333435458074952574136780976169997325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P066 : RatPair2542 := ((1072544910983035121456039516111912597950785785193616370191037546183097443552127613071492867012863 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-230897976372499733289150979044160854806459720021480384351242456242488542519638319087119471789371 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P066 : ℚ := (4974191952915460969856557497452559763863470665315 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P066 :
    phaseExp2646 phaseArg2658P066 20 =
      ((phaseValue2658P066.1,
        phaseValue2658P066.2), phaseRadius2658P066) := by
  decide +kernel

theorem phaseCosPin2658P066 :
    |Real.cos (phaseArg2658P066 : ℝ) -
      (phaseValue2658P066.1 : ℝ)| ≤
        (phaseRadius2658P066 : ℝ) := by
  have hsmall : |((phaseArg2658P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P066]
  have h := phaseExp_cos_error2646 phaseArg2658P066 20 hsmall
  rw [phaseChain2658P066] at h
  simpa [phaseValue2658P066] using h

theorem phaseSinPin2658P066 :
    |Real.sin (phaseArg2658P066 : ℝ) -
      (phaseValue2658P066.2 : ℝ)| ≤
        (phaseRadius2658P066 : ℝ) := by
  have hsmall : |((phaseArg2658P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P066]
  have h := phaseExp_sin_error2646 phaseArg2658P066 20 hsmall
  rw [phaseChain2658P066] at h
  simpa [phaseValue2658P066] using h

end ConnesWeilRH.Dev
