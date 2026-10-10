import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 074 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P074 : ℚ := (-247261172989327558838264439570870316140753857725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P074 : RatPair2542 := ((241270874386274430868867850250724305318840202612730900092299976237233155659864331312999969023649 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1040383832812886125652100897394248986225588648365530601130913722429969541783465090902315586652039 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P074 : ℚ := (15133367088990180178273368409426262133563159341031 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P074 :
    phaseExp2646 phaseArg2658P074 20 =
      ((phaseValue2658P074.1,
        phaseValue2658P074.2), phaseRadius2658P074) := by
  decide +kernel

theorem phaseCosPin2658P074 :
    |Real.cos (phaseArg2658P074 : ℝ) -
      (phaseValue2658P074.1 : ℝ)| ≤
        (phaseRadius2658P074 : ℝ) := by
  have hsmall : |((phaseArg2658P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P074]
  have h := phaseExp_cos_error2646 phaseArg2658P074 20 hsmall
  rw [phaseChain2658P074] at h
  simpa [phaseValue2658P074] using h

theorem phaseSinPin2658P074 :
    |Real.sin (phaseArg2658P074 : ℝ) -
      (phaseValue2658P074.2 : ℝ)| ≤
        (phaseRadius2658P074 : ℝ) := by
  have hsmall : |((phaseArg2658P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P074]
  have h := phaseExp_sin_error2646 phaseArg2658P074 20 hsmall
  rw [phaseChain2658P074] at h
  simpa [phaseValue2658P074] using h

end ConnesWeilRH.Dev
