import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 089 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P089 : ℚ := (-66338363484941540176119727689745694574348595975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P089 : RatPair2542 := ((-168982445592387316426819002728387558445045394116657794586976044199618408013428396966753746276235 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (1013109020161212584158155143191111377151994599030504339929564710937913860772816613680083602341205 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P089 : ℚ := (17153975438422639236182948127643177794685508174055 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P089 :
    phaseExp2646 phaseArg2658P089 20 =
      ((phaseValue2658P089.1,
        phaseValue2658P089.2), phaseRadius2658P089) := by
  decide +kernel

theorem phaseCosPin2658P089 :
    |Real.cos (phaseArg2658P089 : ℝ) -
      (phaseValue2658P089.1 : ℝ)| ≤
        (phaseRadius2658P089 : ℝ) := by
  have hsmall : |((phaseArg2658P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P089]
  have h := phaseExp_cos_error2646 phaseArg2658P089 20 hsmall
  rw [phaseChain2658P089] at h
  simpa [phaseValue2658P089] using h

theorem phaseSinPin2658P089 :
    |Real.sin (phaseArg2658P089 : ℝ) -
      (phaseValue2658P089.2 : ℝ)| ≤
        (phaseRadius2658P089 : ℝ) := by
  have hsmall : |((phaseArg2658P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P089]
  have h := phaseExp_sin_error2646 phaseArg2658P089 20 hsmall
  rw [phaseChain2658P089] at h
  simpa [phaseValue2658P089] using h

end ConnesWeilRH.Dev
