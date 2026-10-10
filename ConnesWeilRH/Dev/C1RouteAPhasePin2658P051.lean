import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 051 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P051 : ℚ := (-524676147562719454120219664455261402542575259075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P051 : RatPair2542 := ((-6353888631829214219919669567480016015391899446110804523400200046268408953209257478643599502631 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (-533845531027847461805589325861360146757347248678039690708533256374661655819222899571856903297489 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P051 : ℚ := (11174912881359020198501396157383199620516687366211 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P051 :
    phaseExp2646 phaseArg2658P051 20 =
      ((phaseValue2658P051.1,
        phaseValue2658P051.2), phaseRadius2658P051) := by
  decide +kernel

theorem phaseCosPin2658P051 :
    |Real.cos (phaseArg2658P051 : ℝ) -
      (phaseValue2658P051.1 : ℝ)| ≤
        (phaseRadius2658P051 : ℝ) := by
  have hsmall : |((phaseArg2658P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P051]
  have h := phaseExp_cos_error2646 phaseArg2658P051 20 hsmall
  rw [phaseChain2658P051] at h
  simpa [phaseValue2658P051] using h

theorem phaseSinPin2658P051 :
    |Real.sin (phaseArg2658P051 : ℝ) -
      (phaseValue2658P051.2 : ℝ)| ≤
        (phaseRadius2658P051 : ℝ) := by
  have hsmall : |((phaseArg2658P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P051]
  have h := phaseExp_sin_error2646 phaseArg2658P051 20 hsmall
  rw [phaseChain2658P051] at h
  simpa [phaseValue2658P051] using h

end ConnesWeilRH.Dev
