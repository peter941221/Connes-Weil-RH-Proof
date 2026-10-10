import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 001 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P001 : ℚ := (-1127752179244006182994035370725676807763926131575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P001 : RatPair2542 := ((1546289007377275275492694160962023484024219077388876283707332318918311932015765178365376688259171 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1473577593235726405426133896896783936629792488570867235891984996111893576480223717684775608926219 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P001 : ℚ := (3565824739404409588344316804517811229705524711189 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P001 :
    phaseExp2646 phaseArg2658P001 20 =
      ((phaseValue2658P001.1,
        phaseValue2658P001.2), phaseRadius2658P001) := by
  decide +kernel

theorem phaseCosPin2658P001 :
    |Real.cos (phaseArg2658P001 : ℝ) -
      (phaseValue2658P001.1 : ℝ)| ≤
        (phaseRadius2658P001 : ℝ) := by
  have hsmall : |((phaseArg2658P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P001]
  have h := phaseExp_cos_error2646 phaseArg2658P001 20 hsmall
  rw [phaseChain2658P001] at h
  simpa [phaseValue2658P001] using h

theorem phaseSinPin2658P001 :
    |Real.sin (phaseArg2658P001 : ℝ) -
      (phaseValue2658P001.2 : ℝ)| ≤
        (phaseRadius2658P001 : ℝ) := by
  have hsmall : |((phaseArg2658P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P001]
  have h := phaseExp_sin_error2646 phaseArg2658P001 20 hsmall
  rw [phaseChain2658P001] at h
  simpa [phaseValue2658P001] using h

end ConnesWeilRH.Dev
