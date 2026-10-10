import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 163 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P163 : ℚ := (826214163403362818557127517590469105153250695325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P163 : RatPair2542 := ((1953265507239719150625810888504443447311254693393474655480629041973547766259337462240458218108145 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (432202058026612673201166724946037369964179772882689887421297762365779789419914863143194225758129 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P163 : ℚ := (4128435652417330970834849461955845789022014151665 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672)

theorem phaseChain2658P163 :
    phaseExp2646 phaseArg2658P163 20 =
      ((phaseValue2658P163.1,
        phaseValue2658P163.2), phaseRadius2658P163) := by
  decide +kernel

theorem phaseCosPin2658P163 :
    |Real.cos (phaseArg2658P163 : ℝ) -
      (phaseValue2658P163.1 : ℝ)| ≤
        (phaseRadius2658P163 : ℝ) := by
  have hsmall : |((phaseArg2658P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P163]
  have h := phaseExp_cos_error2646 phaseArg2658P163 20 hsmall
  rw [phaseChain2658P163] at h
  simpa [phaseValue2658P163] using h

theorem phaseSinPin2658P163 :
    |Real.sin (phaseArg2658P163 : ℝ) -
      (phaseValue2658P163.2 : ℝ)| ≤
        (phaseRadius2658P163 : ℝ) := by
  have hsmall : |((phaseArg2658P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P163]
  have h := phaseExp_sin_error2646 phaseArg2658P163 20 hsmall
  rw [phaseChain2658P163] at h
  simpa [phaseValue2658P163] using h

end ConnesWeilRH.Dev
