import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 033 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P033 : ℚ := (-741783518967982676514793318712610948422261573175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P033 : RatPair2542 := ((-1349118165840090568693428090327762424605863519416145735275431318511179211511904795183471268925859 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1655995408273363872734157765735645360754234384722119385735521294001401225960900569199317746341189 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P033 : ℚ := (61581471097227278664306056045208200798141650562953 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P033 :
    phaseExp2646 phaseArg2658P033 20 =
      ((phaseValue2658P033.1,
        phaseValue2658P033.2), phaseRadius2658P033) := by
  decide +kernel

theorem phaseCosPin2658P033 :
    |Real.cos (phaseArg2658P033 : ℝ) -
      (phaseValue2658P033.1 : ℝ)| ≤
        (phaseRadius2658P033 : ℝ) := by
  have hsmall : |((phaseArg2658P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P033]
  have h := phaseExp_cos_error2646 phaseArg2658P033 20 hsmall
  rw [phaseChain2658P033] at h
  simpa [phaseValue2658P033] using h

theorem phaseSinPin2658P033 :
    |Real.sin (phaseArg2658P033 : ℝ) -
      (phaseValue2658P033.2 : ℝ)| ≤
        (phaseRadius2658P033 : ℝ) := by
  have hsmall : |((phaseArg2658P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P033]
  have h := phaseExp_sin_error2646 phaseArg2658P033 20 hsmall
  rw [phaseChain2658P033] at h
  simpa [phaseValue2658P033] using h

end ConnesWeilRH.Dev
