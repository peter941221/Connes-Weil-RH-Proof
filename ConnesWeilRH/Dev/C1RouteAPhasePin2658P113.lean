import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 113 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P113 : ℚ := (223138131722076089683311811320053699931899822825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P113 : RatPair2542 := ((-996091394351112275279738319671210086393483373161519199576555065391662085438108477409161467866545 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (770485790927271382524114952899743051280186316749516156148874227248416881033826556651324573376631 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P113 : ℚ := (27419601993340365815870325532207078920128898104649 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P113 :
    phaseExp2646 phaseArg2658P113 20 =
      ((phaseValue2658P113.1,
        phaseValue2658P113.2), phaseRadius2658P113) := by
  decide +kernel

theorem phaseCosPin2658P113 :
    |Real.cos (phaseArg2658P113 : ℝ) -
      (phaseValue2658P113.1 : ℝ)| ≤
        (phaseRadius2658P113 : ℝ) := by
  have hsmall : |((phaseArg2658P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P113]
  have h := phaseExp_cos_error2646 phaseArg2658P113 20 hsmall
  rw [phaseChain2658P113] at h
  simpa [phaseValue2658P113] using h

theorem phaseSinPin2658P113 :
    |Real.sin (phaseArg2658P113 : ℝ) -
      (phaseValue2658P113.2 : ℝ)| ≤
        (phaseRadius2658P113 : ℝ) := by
  have hsmall : |((phaseArg2658P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P113]
  have h := phaseExp_sin_error2646 phaseArg2658P113 20 hsmall
  rw [phaseChain2658P113] at h
  simpa [phaseValue2658P113] using h

end ConnesWeilRH.Dev
