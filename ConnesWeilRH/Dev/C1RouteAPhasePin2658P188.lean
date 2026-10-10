import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 188 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P188 : ℚ := (1127752179244006182994035370725676807763926131575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P188 : RatPair2542 := ((773144503688637637746347080481011742012109538694438141853666159459155966007882589182688343392583 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-736788796617863202713066948448391968314896244285433617945992498055946788240111858842387805210971 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P188 : ℚ := (3565824739404409588344316804517811229705524711189 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P188 :
    phaseExp2646 phaseArg2658P188 20 =
      ((phaseValue2658P188.1,
        phaseValue2658P188.2), phaseRadius2658P188) := by
  decide +kernel

theorem phaseCosPin2658P188 :
    |Real.cos (phaseArg2658P188 : ℝ) -
      (phaseValue2658P188.1 : ℝ)| ≤
        (phaseRadius2658P188 : ℝ) := by
  have hsmall : |((phaseArg2658P188 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P188]
  have h := phaseExp_cos_error2646 phaseArg2658P188 20 hsmall
  rw [phaseChain2658P188] at h
  simpa [phaseValue2658P188] using h

theorem phaseSinPin2658P188 :
    |Real.sin (phaseArg2658P188 : ℝ) -
      (phaseValue2658P188.2 : ℝ)| ≤
        (phaseRadius2658P188 : ℝ) := by
  have hsmall : |((phaseArg2658P188 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P188]
  have h := phaseExp_sin_error2646 phaseArg2658P188 20 hsmall
  rw [phaseChain2658P188] at h
  simpa [phaseValue2658P188] using h

end ConnesWeilRH.Dev
