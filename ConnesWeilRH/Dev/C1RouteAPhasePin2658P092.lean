import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 092 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P092 : ℚ := (-30153801584064336443690785313520770261067543625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P092 : RatPair2542 := ((-894225263413867723247303500080489028322078145118280440479767300895053714186840493256940204868117 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1939794266383575560581302525068535436724676771880983675312681048616976992028248547137765608634795 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P092 : ℚ := (231401614889686422375015518194383087315638036085 / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584)

theorem phaseChain2658P092 :
    phaseExp2646 phaseArg2658P092 20 =
      ((phaseValue2658P092.1,
        phaseValue2658P092.2), phaseRadius2658P092) := by
  decide +kernel

theorem phaseCosPin2658P092 :
    |Real.cos (phaseArg2658P092 : ℝ) -
      (phaseValue2658P092.1 : ℝ)| ≤
        (phaseRadius2658P092 : ℝ) := by
  have hsmall : |((phaseArg2658P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P092]
  have h := phaseExp_cos_error2646 phaseArg2658P092 20 hsmall
  rw [phaseChain2658P092] at h
  simpa [phaseValue2658P092] using h

theorem phaseSinPin2658P092 :
    |Real.sin (phaseArg2658P092 : ℝ) -
      (phaseValue2658P092.2 : ℝ)| ≤
        (phaseRadius2658P092 : ℝ) := by
  have hsmall : |((phaseArg2658P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P092]
  have h := phaseExp_sin_error2646 phaseArg2658P092 20 hsmall
  rw [phaseChain2658P092] at h
  simpa [phaseValue2658P092] using h

end ConnesWeilRH.Dev
