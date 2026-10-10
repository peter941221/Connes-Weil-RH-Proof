import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 159 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P159 : ℚ := (777968080868859880247222261088835872735542625525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P159 : RatPair2542 := ((-761357430376759735996424748420513560468589584605469474556625655596720379730774695070897657060069 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (748962627649501785117149485347374886334000974939040434778520670703045980273273662067272892277485 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P159 : ℚ := (60645509116757940840202356454329714553105900446113 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P159 :
    phaseExp2646 phaseArg2658P159 20 =
      ((phaseValue2658P159.1,
        phaseValue2658P159.2), phaseRadius2658P159) := by
  decide +kernel

theorem phaseCosPin2658P159 :
    |Real.cos (phaseArg2658P159 : ℝ) -
      (phaseValue2658P159.1 : ℝ)| ≤
        (phaseRadius2658P159 : ℝ) := by
  have hsmall : |((phaseArg2658P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P159]
  have h := phaseExp_cos_error2646 phaseArg2658P159 20 hsmall
  rw [phaseChain2658P159] at h
  simpa [phaseValue2658P159] using h

theorem phaseSinPin2658P159 :
    |Real.sin (phaseArg2658P159 : ℝ) -
      (phaseValue2658P159.2 : ℝ)| ≤
        (phaseRadius2658P159 : ℝ) := by
  have hsmall : |((phaseArg2658P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P159]
  have h := phaseExp_sin_error2646 phaseArg2658P159 20 hsmall
  rw [phaseChain2658P159] at h
  simpa [phaseValue2658P159] using h

end ConnesWeilRH.Dev
