import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 100 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P100 : ℚ := (66338363484941540176119727689745694574348595975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P100 : RatPair2542 := ((-675929782369549265707276010913550233780181576466631178347904176798473632053713587867014987094315 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-253277255040303146039538785797777844287998649757626084982391177734478465193204153420020900502139 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P100 : ℚ := (17153975438422639236182948127643177794685508174055 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P100 :
    phaseExp2646 phaseArg2658P100 20 =
      ((phaseValue2658P100.1,
        phaseValue2658P100.2), phaseRadius2658P100) := by
  decide +kernel

theorem phaseCosPin2658P100 :
    |Real.cos (phaseArg2658P100 : ℝ) -
      (phaseValue2658P100.1 : ℝ)| ≤
        (phaseRadius2658P100 : ℝ) := by
  have hsmall : |((phaseArg2658P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P100]
  have h := phaseExp_cos_error2646 phaseArg2658P100 20 hsmall
  rw [phaseChain2658P100] at h
  simpa [phaseValue2658P100] using h

theorem phaseSinPin2658P100 :
    |Real.sin (phaseArg2658P100 : ℝ) -
      (phaseValue2658P100.2 : ℝ)| ≤
        (phaseRadius2658P100 : ℝ) := by
  have hsmall : |((phaseArg2658P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P100]
  have h := phaseExp_sin_error2646 phaseArg2658P100 20 hsmall
  rw [phaseChain2658P100] at h
  simpa [phaseValue2658P100] using h

end ConnesWeilRH.Dev
