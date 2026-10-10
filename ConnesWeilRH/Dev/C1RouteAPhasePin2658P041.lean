import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 041 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P041 : ℚ := (-645291353898976799894982805709344483586845433575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P041 : RatPair2542 := ((1058529638206384042937469139224947747692663856945404391056223806352597571421153441884868739280267 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (35465792889249730633311621963135453243120629175917395002079313409453716346714171683331949128303 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P041 : ℚ := (71056905658117577367210621956450172855480904155 / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896)

theorem phaseChain2658P041 :
    phaseExp2646 phaseArg2658P041 20 =
      ((phaseValue2658P041.1,
        phaseValue2658P041.2), phaseRadius2658P041) := by
  decide +kernel

theorem phaseCosPin2658P041 :
    |Real.cos (phaseArg2658P041 : ℝ) -
      (phaseValue2658P041.1 : ℝ)| ≤
        (phaseRadius2658P041 : ℝ) := by
  have hsmall : |((phaseArg2658P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P041]
  have h := phaseExp_cos_error2646 phaseArg2658P041 20 hsmall
  rw [phaseChain2658P041] at h
  simpa [phaseValue2658P041] using h

theorem phaseSinPin2658P041 :
    |Real.sin (phaseArg2658P041 : ℝ) -
      (phaseValue2658P041.2 : ℝ)| ≤
        (phaseRadius2658P041 : ℝ) := by
  have hsmall : |((phaseArg2658P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P041]
  have h := phaseExp_sin_error2646 phaseArg2658P041 20 hsmall
  rw [phaseChain2658P041] at h
  simpa [phaseValue2658P041] using h

end ConnesWeilRH.Dev
