import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 024 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P024 : ℚ := (-850337204670614287712080145841285721362104730225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P024 : RatPair2542 := ((-906421138278150289115380889897693804746745895600799475191279323621258592581131155992309630676691 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-564810476609713001340639311227339713677282075711323599162709241957090541701501602562237677317659 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P024 : ℚ := (36943563153503766835221569033775776317865838571515 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P024 :
    phaseExp2646 phaseArg2658P024 20 =
      ((phaseValue2658P024.1,
        phaseValue2658P024.2), phaseRadius2658P024) := by
  decide +kernel

theorem phaseCosPin2658P024 :
    |Real.cos (phaseArg2658P024 : ℝ) -
      (phaseValue2658P024.1 : ℝ)| ≤
        (phaseRadius2658P024 : ℝ) := by
  have hsmall : |((phaseArg2658P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P024]
  have h := phaseExp_cos_error2646 phaseArg2658P024 20 hsmall
  rw [phaseChain2658P024] at h
  simpa [phaseValue2658P024] using h

theorem phaseSinPin2658P024 :
    |Real.sin (phaseArg2658P024 : ℝ) -
      (phaseValue2658P024.2 : ℝ)| ≤
        (phaseRadius2658P024 : ℝ) := by
  have hsmall : |((phaseArg2658P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P024]
  have h := phaseExp_sin_error2646 phaseArg2658P024 20 hsmall
  rw [phaseChain2658P024] at h
  simpa [phaseValue2658P024] using h

end ConnesWeilRH.Dev
