import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 148 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P148 : ℚ := (645291353898976799894982805709344483586845433575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P148 : RatPair2542 := ((2117059276412768085874938278449895495385327713890808782112447612705195142842306883769737478262783 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-283726343113997845066492975705083625944965033407339160016634507275629730773713373466655595104817 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P148 : ℚ := (71056905658117577367210621956450172855480904155 / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896)

theorem phaseChain2658P148 :
    phaseExp2646 phaseArg2658P148 20 =
      ((phaseValue2658P148.1,
        phaseValue2658P148.2), phaseRadius2658P148) := by
  decide +kernel

theorem phaseCosPin2658P148 :
    |Real.cos (phaseArg2658P148 : ℝ) -
      (phaseValue2658P148.1 : ℝ)| ≤
        (phaseRadius2658P148 : ℝ) := by
  have hsmall : |((phaseArg2658P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P148]
  have h := phaseExp_cos_error2646 phaseArg2658P148 20 hsmall
  rw [phaseChain2658P148] at h
  simpa [phaseValue2658P148] using h

theorem phaseSinPin2658P148 :
    |Real.sin (phaseArg2658P148 : ℝ) -
      (phaseValue2658P148.2 : ℝ)| ≤
        (phaseRadius2658P148 : ℝ) := by
  have hsmall : |((phaseArg2658P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P148]
  have h := phaseExp_sin_error2646 phaseArg2658P148 20 hsmall
  rw [phaseChain2658P148] at h
  simpa [phaseValue2658P148] using h

end ConnesWeilRH.Dev
