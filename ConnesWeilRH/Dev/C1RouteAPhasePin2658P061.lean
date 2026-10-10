import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 061 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P061 : ℚ := (-404060941226462108345456523201178321498305084575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P061 : RatPair2542 := ((-2101161290427734255402259801351247949908323292009554048277519120726216420298898591347287393517725 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (48017224974197703060464747360895152535741848164517009352624623980897280477702402728655410395339 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P061 : ℚ := (38743662471349502041470797624355987075678536835387 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P061 :
    phaseExp2646 phaseArg2658P061 20 =
      ((phaseValue2658P061.1,
        phaseValue2658P061.2), phaseRadius2658P061) := by
  decide +kernel

theorem phaseCosPin2658P061 :
    |Real.cos (phaseArg2658P061 : ℝ) -
      (phaseValue2658P061.1 : ℝ)| ≤
        (phaseRadius2658P061 : ℝ) := by
  have hsmall : |((phaseArg2658P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P061]
  have h := phaseExp_cos_error2646 phaseArg2658P061 20 hsmall
  rw [phaseChain2658P061] at h
  simpa [phaseValue2658P061] using h

theorem phaseSinPin2658P061 :
    |Real.sin (phaseArg2658P061 : ℝ) -
      (phaseValue2658P061.2 : ℝ)| ≤
        (phaseRadius2658P061 : ℝ) := by
  have hsmall : |((phaseArg2658P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P061]
  have h := phaseExp_sin_error2646 phaseArg2658P061 20 hsmall
  rw [phaseChain2658P061] at h
  simpa [phaseValue2658P061] using h

end ConnesWeilRH.Dev
