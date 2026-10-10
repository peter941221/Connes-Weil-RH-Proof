import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 090 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P090 : ℚ := (-54276842851315805598643413564337386469921578525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P090 : RatPair2542 := ((131686967372172408920642386459354902410758707053406405101991947972537969258309005730770253153315 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-175376401953211385068199018960137758991600290243743513621436802310976130319763419873310502869499 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P090 : ℚ := (3174551260284407825768131336670247410596966452123 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P090 :
    phaseExp2646 phaseArg2658P090 20 =
      ((phaseValue2658P090.1,
        phaseValue2658P090.2), phaseRadius2658P090) := by
  decide +kernel

theorem phaseCosPin2658P090 :
    |Real.cos (phaseArg2658P090 : ℝ) -
      (phaseValue2658P090.1 : ℝ)| ≤
        (phaseRadius2658P090 : ℝ) := by
  have hsmall : |((phaseArg2658P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P090]
  have h := phaseExp_cos_error2646 phaseArg2658P090 20 hsmall
  rw [phaseChain2658P090] at h
  simpa [phaseValue2658P090] using h

theorem phaseSinPin2658P090 :
    |Real.sin (phaseArg2658P090 : ℝ) -
      (phaseValue2658P090.2 : ℝ)| ≤
        (phaseRadius2658P090 : ℝ) := by
  have hsmall : |((phaseArg2658P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P090]
  have h := phaseExp_sin_error2646 phaseArg2658P090 20 hsmall
  rw [phaseChain2658P090] at h
  simpa [phaseValue2658P090] using h

end ConnesWeilRH.Dev
