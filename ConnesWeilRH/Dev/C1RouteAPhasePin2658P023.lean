import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 023 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P023 : ℚ := (-862398725304240022289556459966694029466531747675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P023 : RatPair2542 := ((1846597254944190829454606443956642941973629256601581981889862665587629025699076089873279063244509 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1073554467949705063265326817349189837264893884220840622615424001497285169120907460140347786762931 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P023 : ℚ := (4377616223893292765648792440558184250707780851301 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P023 :
    phaseExp2646 phaseArg2658P023 20 =
      ((phaseValue2658P023.1,
        phaseValue2658P023.2), phaseRadius2658P023) := by
  decide +kernel

theorem phaseCosPin2658P023 :
    |Real.cos (phaseArg2658P023 : ℝ) -
      (phaseValue2658P023.1 : ℝ)| ≤
        (phaseRadius2658P023 : ℝ) := by
  have hsmall : |((phaseArg2658P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P023]
  have h := phaseExp_cos_error2646 phaseArg2658P023 20 hsmall
  rw [phaseChain2658P023] at h
  simpa [phaseValue2658P023] using h

theorem phaseSinPin2658P023 :
    |Real.sin (phaseArg2658P023 : ℝ) -
      (phaseValue2658P023.2 : ℝ)| ≤
        (phaseRadius2658P023 : ℝ) := by
  have hsmall : |((phaseArg2658P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P023]
  have h := phaseExp_sin_error2646 phaseArg2658P023 20 hsmall
  rw [phaseChain2658P023] at h
  simpa [phaseValue2658P023] using h

end ConnesWeilRH.Dev
