import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 019 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P019 : ℚ := (-910644807838742960599461716468327261884239817475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P019 : RatPair2542 := ((159217046849307646319404199703736569963774534485270672964295616926873868328876660603174002020579 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1056058751395079429439103738580209390120857666955799006182366998761427729509763153143359174883515 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P019 : ℚ := (64434626149014444608444449341741487277254221573221 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P019 :
    phaseExp2646 phaseArg2658P019 20 =
      ((phaseValue2658P019.1,
        phaseValue2658P019.2), phaseRadius2658P019) := by
  decide +kernel

theorem phaseCosPin2658P019 :
    |Real.cos (phaseArg2658P019 : ℝ) -
      (phaseValue2658P019.1 : ℝ)| ≤
        (phaseRadius2658P019 : ℝ) := by
  have hsmall : |((phaseArg2658P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P019]
  have h := phaseExp_cos_error2646 phaseArg2658P019 20 hsmall
  rw [phaseChain2658P019] at h
  simpa [phaseValue2658P019] using h

theorem phaseSinPin2658P019 :
    |Real.sin (phaseArg2658P019 : ℝ) -
      (phaseValue2658P019.2 : ℝ)| ≤
        (phaseRadius2658P019 : ℝ) := by
  have hsmall : |((phaseArg2658P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P019]
  have h := phaseExp_sin_error2646 phaseArg2658P019 20 hsmall
  rw [phaseChain2658P019] at h
  simpa [phaseValue2658P019] using h

end ConnesWeilRH.Dev
