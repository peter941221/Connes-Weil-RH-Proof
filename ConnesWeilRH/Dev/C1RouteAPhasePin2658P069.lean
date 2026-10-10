import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 069 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P069 : ℚ := (-307568776157456231725646010197911856662888944975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P069 : RatPair2542 := ((9912463951637906615682629493199499507056938235826909664502992851289698773563313517096833815671 / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), (-214789100288309389404238599145216830653989583837533300337209279729928284761100411863761598869091 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P069 : ℚ := (29361377514038054947182645338410195353984010858891 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P069 :
    phaseExp2646 phaseArg2658P069 20 =
      ((phaseValue2658P069.1,
        phaseValue2658P069.2), phaseRadius2658P069) := by
  decide +kernel

theorem phaseCosPin2658P069 :
    |Real.cos (phaseArg2658P069 : ℝ) -
      (phaseValue2658P069.1 : ℝ)| ≤
        (phaseRadius2658P069 : ℝ) := by
  have hsmall : |((phaseArg2658P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P069]
  have h := phaseExp_cos_error2646 phaseArg2658P069 20 hsmall
  rw [phaseChain2658P069] at h
  simpa [phaseValue2658P069] using h

theorem phaseSinPin2658P069 :
    |Real.sin (phaseArg2658P069 : ℝ) -
      (phaseValue2658P069.2 : ℝ)| ≤
        (phaseRadius2658P069 : ℝ) := by
  have hsmall : |((phaseArg2658P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P069]
  have h := phaseExp_sin_error2646 phaseArg2658P069 20 hsmall
  rw [phaseChain2658P069] at h
  simpa [phaseValue2658P069] using h

end ConnesWeilRH.Dev
