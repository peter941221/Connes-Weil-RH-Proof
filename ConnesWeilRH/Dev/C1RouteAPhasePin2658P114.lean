import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 114 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P114 : ℚ := (235199652355701824260788125445462008036326840275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P114 : RatPair2542 := ((806561464758949405803957721015369274624811537159670585679201248563786864247681295102093889961473 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1400098222227921865580315169830949054717653604701973916572648607647787055101596181358607256835773 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P114 : ℚ := (7675855939046681605717650908044294701300385196865 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P114 :
    phaseExp2646 phaseArg2658P114 20 =
      ((phaseValue2658P114.1,
        phaseValue2658P114.2), phaseRadius2658P114) := by
  decide +kernel

theorem phaseCosPin2658P114 :
    |Real.cos (phaseArg2658P114 : ℝ) -
      (phaseValue2658P114.1 : ℝ)| ≤
        (phaseRadius2658P114 : ℝ) := by
  have hsmall : |((phaseArg2658P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P114]
  have h := phaseExp_cos_error2646 phaseArg2658P114 20 hsmall
  rw [phaseChain2658P114] at h
  simpa [phaseValue2658P114] using h

theorem phaseSinPin2658P114 :
    |Real.sin (phaseArg2658P114 : ℝ) -
      (phaseValue2658P114.2 : ℝ)| ≤
        (phaseRadius2658P114 : ℝ) := by
  have hsmall : |((phaseArg2658P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P114]
  have h := phaseExp_sin_error2646 phaseArg2658P114 20 hsmall
  rw [phaseChain2658P114] at h
  simpa [phaseValue2658P114] using h

end ConnesWeilRH.Dev
