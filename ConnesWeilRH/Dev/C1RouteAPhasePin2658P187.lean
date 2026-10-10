import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 187 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P187 : ℚ := (1115690658610380448416559056600268499659499114125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P187 : RatPair2542 := ((289376870621022628135406010437924298137954125077268527708659819558609750090229029395950078824945 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (2056084804822148123271326368559452973164682033083282138066917933957778114296380514499820528771145 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P187 : ℚ := (8428852498523815158290364261319943752488434274949 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P187 :
    phaseExp2646 phaseArg2658P187 20 =
      ((phaseValue2658P187.1,
        phaseValue2658P187.2), phaseRadius2658P187) := by
  decide +kernel

theorem phaseCosPin2658P187 :
    |Real.cos (phaseArg2658P187 : ℝ) -
      (phaseValue2658P187.1 : ℝ)| ≤
        (phaseRadius2658P187 : ℝ) := by
  have hsmall : |((phaseArg2658P187 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P187]
  have h := phaseExp_cos_error2646 phaseArg2658P187 20 hsmall
  rw [phaseChain2658P187] at h
  simpa [phaseValue2658P187] using h

theorem phaseSinPin2658P187 :
    |Real.sin (phaseArg2658P187 : ℝ) -
      (phaseValue2658P187.2 : ℝ)| ≤
        (phaseRadius2658P187 : ℝ) := by
  have hsmall : |((phaseArg2658P187 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P187]
  have h := phaseExp_sin_error2646 phaseArg2658P187 20 hsmall
  rw [phaseChain2658P187] at h
  simpa [phaseValue2658P187] using h

end ConnesWeilRH.Dev
