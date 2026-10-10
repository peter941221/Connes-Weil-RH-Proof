import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 156 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P156 : ℚ := (741783518967982676514793318712610948422261573175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P156 : RatPair2542 := ((-674559082920045284346714045163881212302931759708072867637715659255589605755952397591735633644967 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1655995408273363872734157765735645360754234384722119385735521294001401225960900569199317747650087 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P156 : ℚ := (61581471097227278664306056045208200798141650562953 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P156 :
    phaseExp2646 phaseArg2658P156 20 =
      ((phaseValue2658P156.1,
        phaseValue2658P156.2), phaseRadius2658P156) := by
  decide +kernel

theorem phaseCosPin2658P156 :
    |Real.cos (phaseArg2658P156 : ℝ) -
      (phaseValue2658P156.1 : ℝ)| ≤
        (phaseRadius2658P156 : ℝ) := by
  have hsmall : |((phaseArg2658P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P156]
  have h := phaseExp_cos_error2646 phaseArg2658P156 20 hsmall
  rw [phaseChain2658P156] at h
  simpa [phaseValue2658P156] using h

theorem phaseSinPin2658P156 :
    |Real.sin (phaseArg2658P156 : ℝ) -
      (phaseValue2658P156.2 : ℝ)| ≤
        (phaseRadius2658P156 : ℝ) := by
  have hsmall : |((phaseArg2658P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P156]
  have h := phaseExp_sin_error2646 phaseArg2658P156 20 hsmall
  rw [phaseChain2658P156] at h
  simpa [phaseValue2658P156] using h

end ConnesWeilRH.Dev
