import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 068 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P068 : ℚ := (-319630296791081966303122324323320164767315962425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P068 : RatPair2542 := ((462444565866999206682056786265713517979879859856033212909689154010968577046555335226728539478241 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (240670311046256731279932444902630095685003392923199744026962432324699852653285728631571771711283 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P068 : ℚ := (30171173685331022731454679666516502336172740515335 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P068 :
    phaseExp2646 phaseArg2658P068 20 =
      ((phaseValue2658P068.1,
        phaseValue2658P068.2), phaseRadius2658P068) := by
  decide +kernel

theorem phaseCosPin2658P068 :
    |Real.cos (phaseArg2658P068 : ℝ) -
      (phaseValue2658P068.1 : ℝ)| ≤
        (phaseRadius2658P068 : ℝ) := by
  have hsmall : |((phaseArg2658P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P068]
  have h := phaseExp_cos_error2646 phaseArg2658P068 20 hsmall
  rw [phaseChain2658P068] at h
  simpa [phaseValue2658P068] using h

theorem phaseSinPin2658P068 :
    |Real.sin (phaseArg2658P068 : ℝ) -
      (phaseValue2658P068.2 : ℝ)| ≤
        (phaseRadius2658P068 : ℝ) := by
  have hsmall : |((phaseArg2658P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P068]
  have h := phaseExp_sin_error2646 phaseArg2658P068 20 hsmall
  rw [phaseChain2658P068] at h
  simpa [phaseValue2658P068] using h

end ConnesWeilRH.Dev
