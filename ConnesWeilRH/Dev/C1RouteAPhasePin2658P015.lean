import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 015 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P015 : ℚ := (-958890890373245898909366972969960494301947887275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P015 : RatPair2542 := ((-1040515562117912364059167690946840133569380571103154782642075561316877891823983499209693453783167 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-60175534582167226650693160473714662884361622531222186351233983272473912922459393022779142441097 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P015 : ℚ := (14316274521101012571812059360092715156739379547839 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P015 :
    phaseExp2646 phaseArg2658P015 20 =
      ((phaseValue2658P015.1,
        phaseValue2658P015.2), phaseRadius2658P015) := by
  decide +kernel

theorem phaseCosPin2658P015 :
    |Real.cos (phaseArg2658P015 : ℝ) -
      (phaseValue2658P015.1 : ℝ)| ≤
        (phaseRadius2658P015 : ℝ) := by
  have hsmall : |((phaseArg2658P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P015]
  have h := phaseExp_cos_error2646 phaseArg2658P015 20 hsmall
  rw [phaseChain2658P015] at h
  simpa [phaseValue2658P015] using h

theorem phaseSinPin2658P015 :
    |Real.sin (phaseArg2658P015 : ℝ) -
      (phaseValue2658P015.2 : ℝ)| ≤
        (phaseRadius2658P015 : ℝ) := by
  have hsmall : |((phaseArg2658P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P015]
  have h := phaseExp_sin_error2646 phaseArg2658P015 20 hsmall
  rw [phaseChain2658P015] at h
  simpa [phaseValue2658P015] using h

end ConnesWeilRH.Dev
