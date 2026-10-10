import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 034 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P034 : ℚ := (-729721998334356941937317004587202640317834555725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P034 : RatPair2542 := ((-416114982912521206621102923971604839638327732717677801445884227048624713055874239902184339986391 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1967189340558006367413762138743675946763378303054475747934263167949816514359704664047530786605471 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P034 : ℚ := (25865296924285929711408452886165287067762519460841 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P034 :
    phaseExp2646 phaseArg2658P034 20 =
      ((phaseValue2658P034.1,
        phaseValue2658P034.2), phaseRadius2658P034) := by
  decide +kernel

theorem phaseCosPin2658P034 :
    |Real.cos (phaseArg2658P034 : ℝ) -
      (phaseValue2658P034.1 : ℝ)| ≤
        (phaseRadius2658P034 : ℝ) := by
  have hsmall : |((phaseArg2658P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P034]
  have h := phaseExp_cos_error2646 phaseArg2658P034 20 hsmall
  rw [phaseChain2658P034] at h
  simpa [phaseValue2658P034] using h

theorem phaseSinPin2658P034 :
    |Real.sin (phaseArg2658P034 : ℝ) -
      (phaseValue2658P034.2 : ℝ)| ≤
        (phaseRadius2658P034 : ℝ) := by
  have hsmall : |((phaseArg2658P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P034]
  have h := phaseExp_sin_error2646 phaseArg2658P034 20 hsmall
  rw [phaseChain2658P034] at h
  simpa [phaseValue2658P034] using h

end ConnesWeilRH.Dev
