import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 123 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P123 : ℚ := (343753338058333435458074952574136780976169997325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P123 : RatPair2542 := ((536272455491517560728019758055956298975392892596808185095518773091548721776063806535746434411353 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (923591905489998933156603916176643419225838880085921537404969824969954170078553276348477886627069 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P123 : ℚ := (4974191952915460969856557497452559763863470665315 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P123 :
    phaseExp2646 phaseArg2658P123 20 =
      ((phaseValue2658P123.1,
        phaseValue2658P123.2), phaseRadius2658P123) := by
  decide +kernel

theorem phaseCosPin2658P123 :
    |Real.cos (phaseArg2658P123 : ℝ) -
      (phaseValue2658P123.1 : ℝ)| ≤
        (phaseRadius2658P123 : ℝ) := by
  have hsmall : |((phaseArg2658P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P123]
  have h := phaseExp_cos_error2646 phaseArg2658P123 20 hsmall
  rw [phaseChain2658P123] at h
  simpa [phaseValue2658P123] using h

theorem phaseSinPin2658P123 :
    |Real.sin (phaseArg2658P123 : ℝ) -
      (phaseValue2658P123.2 : ℝ)| ≤
        (phaseRadius2658P123 : ℝ) := by
  have hsmall : |((phaseArg2658P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P123]
  have h := phaseExp_sin_error2646 phaseArg2658P123 20 hsmall
  rw [phaseChain2658P123] at h
  simpa [phaseValue2658P123] using h

end ConnesWeilRH.Dev
