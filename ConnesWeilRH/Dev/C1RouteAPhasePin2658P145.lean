import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 145 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P145 : ℚ := (609106791998099596162553863333119559273564381225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P145 : RatPair2542 := ((2073131311737318394271273445735225064642867882626268910955751694394828784463325698220204701561681 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-64295118146289497080265984579764731576227111390566972058915251333846481967314224809914058374333 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P145 : ℚ := (5201750449836831549246966466520156324088109928305 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P145 :
    phaseExp2646 phaseArg2658P145 20 =
      ((phaseValue2658P145.1,
        phaseValue2658P145.2), phaseRadius2658P145) := by
  decide +kernel

theorem phaseCosPin2658P145 :
    |Real.cos (phaseArg2658P145 : ℝ) -
      (phaseValue2658P145.1 : ℝ)| ≤
        (phaseRadius2658P145 : ℝ) := by
  have hsmall : |((phaseArg2658P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P145]
  have h := phaseExp_cos_error2646 phaseArg2658P145 20 hsmall
  rw [phaseChain2658P145] at h
  simpa [phaseValue2658P145] using h

theorem phaseSinPin2658P145 :
    |Real.sin (phaseArg2658P145 : ℝ) -
      (phaseValue2658P145.2 : ℝ)| ≤
        (phaseRadius2658P145 : ℝ) := by
  have hsmall : |((phaseArg2658P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P145]
  have h := phaseExp_sin_error2646 phaseArg2658P145 20 hsmall
  rw [phaseChain2658P145] at h
  simpa [phaseValue2658P145] using h

end ConnesWeilRH.Dev
