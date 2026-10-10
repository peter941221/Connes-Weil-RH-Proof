import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 110 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P110 : ℚ := (186953569821198885950882868943828775618618770475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P110 : RatPair2542 := ((-236948379590147189546366035926684425400992280962635383855277893536126618610462894617526336934637 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (984474684203113686519642676822972128142160181103360332629267705596556571167798262443310032323839 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P110 : ℚ := (7932812058581425553412225079029946931964629266725 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P110 :
    phaseExp2646 phaseArg2658P110 20 =
      ((phaseValue2658P110.1,
        phaseValue2658P110.2), phaseRadius2658P110) := by
  decide +kernel

theorem phaseCosPin2658P110 :
    |Real.cos (phaseArg2658P110 : ℝ) -
      (phaseValue2658P110.1 : ℝ)| ≤
        (phaseRadius2658P110 : ℝ) := by
  have hsmall : |((phaseArg2658P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P110]
  have h := phaseExp_cos_error2646 phaseArg2658P110 20 hsmall
  rw [phaseChain2658P110] at h
  simpa [phaseValue2658P110] using h

theorem phaseSinPin2658P110 :
    |Real.sin (phaseArg2658P110 : ℝ) -
      (phaseValue2658P110.2 : ℝ)| ≤
        (phaseRadius2658P110 : ℝ) := by
  have hsmall : |((phaseArg2658P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P110]
  have h := phaseExp_sin_error2646 phaseArg2658P110 20 hsmall
  rw [phaseChain2658P110] at h
  simpa [phaseValue2658P110] using h

end ConnesWeilRH.Dev
