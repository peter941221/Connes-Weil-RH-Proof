import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 044 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P044 : ℚ := (-609106791998099596162553863333119559273564381225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P044 : RatPair2542 := ((2073131311737318394271273445735225064642867882626268910955751694394828784463325698220204702082581 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (514360945170315976642127876638117852609816891124535776471322010670771855738513798479312464961743 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P044 : ℚ := (5201750449836831549246966466520156324088109928305 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P044 :
    phaseExp2646 phaseArg2658P044 20 =
      ((phaseValue2658P044.1,
        phaseValue2658P044.2), phaseRadius2658P044) := by
  decide +kernel

theorem phaseCosPin2658P044 :
    |Real.cos (phaseArg2658P044 : ℝ) -
      (phaseValue2658P044.1 : ℝ)| ≤
        (phaseRadius2658P044 : ℝ) := by
  have hsmall : |((phaseArg2658P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P044]
  have h := phaseExp_cos_error2646 phaseArg2658P044 20 hsmall
  rw [phaseChain2658P044] at h
  simpa [phaseValue2658P044] using h

theorem phaseSinPin2658P044 :
    |Real.sin (phaseArg2658P044 : ℝ) -
      (phaseValue2658P044.2 : ℝ)| ≤
        (phaseRadius2658P044 : ℝ) := by
  have hsmall : |((phaseArg2658P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P044]
  have h := phaseExp_sin_error2646 phaseArg2658P044 20 hsmall
  rw [phaseChain2658P044] at h
  simpa [phaseValue2658P044] using h

end ConnesWeilRH.Dev
