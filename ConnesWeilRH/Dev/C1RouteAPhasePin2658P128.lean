import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 128 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P128 : ℚ := (404060941226462108345456523201178321498305084575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P128 : RatPair2542 := ((-1050580645213867127701129900675623974954161646004777024138759560363108210149449295673643696937411 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-384137799793581624483717978887161220285934785316136074820996991847178243821619221829243281096753 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P128 : ℚ := (38743662471349502041470797624355987075678536835387 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P128 :
    phaseExp2646 phaseArg2658P128 20 =
      ((phaseValue2658P128.1,
        phaseValue2658P128.2), phaseRadius2658P128) := by
  decide +kernel

theorem phaseCosPin2658P128 :
    |Real.cos (phaseArg2658P128 : ℝ) -
      (phaseValue2658P128.1 : ℝ)| ≤
        (phaseRadius2658P128 : ℝ) := by
  have hsmall : |((phaseArg2658P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P128]
  have h := phaseExp_cos_error2646 phaseArg2658P128 20 hsmall
  rw [phaseChain2658P128] at h
  simpa [phaseValue2658P128] using h

theorem phaseSinPin2658P128 :
    |Real.sin (phaseArg2658P128 : ℝ) -
      (phaseValue2658P128.2 : ℝ)| ≤
        (phaseRadius2658P128 : ℝ) := by
  have hsmall : |((phaseArg2658P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P128]
  have h := phaseExp_sin_error2646 phaseArg2658P128 20 hsmall
  rw [phaseChain2658P128] at h
  simpa [phaseValue2658P128] using h

end ConnesWeilRH.Dev
