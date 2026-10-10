import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 103 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P103 : ℚ := (102522925385818743908548670065970618887629648325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P103 : RatPair2542 := ((-224733964167507993983319592044802187955389259338913147617827592454503568843517571892500167950777 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-2088161679329554249401550624810522268373109279642582058526747188343019681238536594520048084993879 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P103 : ℚ := (25122967905684723159398264284424186908706871961541 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P103 :
    phaseExp2646 phaseArg2658P103 20 =
      ((phaseValue2658P103.1,
        phaseValue2658P103.2), phaseRadius2658P103) := by
  decide +kernel

theorem phaseCosPin2658P103 :
    |Real.cos (phaseArg2658P103 : ℝ) -
      (phaseValue2658P103.1 : ℝ)| ≤
        (phaseRadius2658P103 : ℝ) := by
  have hsmall : |((phaseArg2658P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P103]
  have h := phaseExp_cos_error2646 phaseArg2658P103 20 hsmall
  rw [phaseChain2658P103] at h
  simpa [phaseValue2658P103] using h

theorem phaseSinPin2658P103 :
    |Real.sin (phaseArg2658P103 : ℝ) -
      (phaseValue2658P103.2 : ℝ)| ≤
        (phaseRadius2658P103 : ℝ) := by
  have hsmall : |((phaseArg2658P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P103]
  have h := phaseExp_sin_error2646 phaseArg2658P103 20 hsmall
  rw [phaseChain2658P103] at h
  simpa [phaseValue2658P103] using h

end ConnesWeilRH.Dev
