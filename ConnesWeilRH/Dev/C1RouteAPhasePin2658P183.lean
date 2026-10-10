import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 183 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P183 : ℚ := (1067444576075877510106653800098635267241791044325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P183 : RatPair2542 := ((-1062378774912121377666287918934012798500769165490997467558687048667047172538930433756150563789301 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-109368610770041995352957938872063428977930980642184866346607102366675857209316220419783159424915 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P183 : ℚ := (38082977885313918245754348572741303299181413926991 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P183 :
    phaseExp2646 phaseArg2658P183 20 =
      ((phaseValue2658P183.1,
        phaseValue2658P183.2), phaseRadius2658P183) := by
  decide +kernel

theorem phaseCosPin2658P183 :
    |Real.cos (phaseArg2658P183 : ℝ) -
      (phaseValue2658P183.1 : ℝ)| ≤
        (phaseRadius2658P183 : ℝ) := by
  have hsmall : |((phaseArg2658P183 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P183]
  have h := phaseExp_cos_error2646 phaseArg2658P183 20 hsmall
  rw [phaseChain2658P183] at h
  simpa [phaseValue2658P183] using h

theorem phaseSinPin2658P183 :
    |Real.sin (phaseArg2658P183 : ℝ) -
      (phaseValue2658P183.2 : ℝ)| ≤
        (phaseRadius2658P183 : ℝ) := by
  have hsmall : |((phaseArg2658P183 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P183]
  have h := phaseExp_sin_error2646 phaseArg2658P183 20 hsmall
  rw [phaseChain2658P183] at h
  simpa [phaseValue2658P183] using h

end ConnesWeilRH.Dev
