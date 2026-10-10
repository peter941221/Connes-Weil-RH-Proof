import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 099 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P099 : ℚ := (54276842851315805598643413564337386469921578525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P099 : RatPair2542 := ((2106991477954758542730278183349678438572139312854502481631871167560607508132944091692324050790181 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (175376401953211385068199018960137758991600290243743513621436802310976130319763419873310501834517 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P099 : ℚ := (3174551260284407825768131336670247410596966452123 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P099 :
    phaseExp2646 phaseArg2658P099 20 =
      ((phaseValue2658P099.1,
        phaseValue2658P099.2), phaseRadius2658P099) := by
  decide +kernel

theorem phaseCosPin2658P099 :
    |Real.cos (phaseArg2658P099 : ℝ) -
      (phaseValue2658P099.1 : ℝ)| ≤
        (phaseRadius2658P099 : ℝ) := by
  have hsmall : |((phaseArg2658P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P099]
  have h := phaseExp_cos_error2646 phaseArg2658P099 20 hsmall
  rw [phaseChain2658P099] at h
  simpa [phaseValue2658P099] using h

theorem phaseSinPin2658P099 :
    |Real.sin (phaseArg2658P099 : ℝ) -
      (phaseValue2658P099.2 : ℝ)| ≤
        (phaseRadius2658P099 : ℝ) := by
  have hsmall : |((phaseArg2658P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P099]
  have h := phaseExp_sin_error2646 phaseArg2658P099 20 hsmall
  rw [phaseChain2658P099] at h
  simpa [phaseValue2658P099] using h

end ConnesWeilRH.Dev
