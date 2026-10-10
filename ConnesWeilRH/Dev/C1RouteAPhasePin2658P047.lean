import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 047 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P047 : ℚ := (-572922230097222392430124920956894634960283328875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P047 : RatPair2542 := ((250519552575565287895724057254174221259852194458290375987148846915707448978880386808176237442965 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (184695299644418453394403859319606366025816328330080722957027799923781112624904452903630107523753 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P047 : ℚ := (9656855431439923701256525214099434356054710189113 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P047 :
    phaseExp2646 phaseArg2658P047 20 =
      ((phaseValue2658P047.1,
        phaseValue2658P047.2), phaseRadius2658P047) := by
  decide +kernel

theorem phaseCosPin2658P047 :
    |Real.cos (phaseArg2658P047 : ℝ) -
      (phaseValue2658P047.1 : ℝ)| ≤
        (phaseRadius2658P047 : ℝ) := by
  have hsmall : |((phaseArg2658P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P047]
  have h := phaseExp_cos_error2646 phaseArg2658P047 20 hsmall
  rw [phaseChain2658P047] at h
  simpa [phaseValue2658P047] using h

theorem phaseSinPin2658P047 :
    |Real.sin (phaseArg2658P047 : ℝ) -
      (phaseValue2658P047.2 : ℝ)| ≤
        (phaseRadius2658P047 : ℝ) := by
  have hsmall : |((phaseArg2658P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P047]
  have h := phaseExp_sin_error2646 phaseArg2658P047 20 hsmall
  rw [phaseChain2658P047] at h
  simpa [phaseValue2658P047] using h

end ConnesWeilRH.Dev
