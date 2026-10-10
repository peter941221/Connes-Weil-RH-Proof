import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 155 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P155 : ℚ := (729721998334356941937317004587202640317834555725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P155 : RatPair2542 := ((-416114982912521206621102923971604839638327732717677801445884227048624713055874239902184340950623 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-983594670279003183706881069371837973381689151527237873967131583974908257179852332023765392885973 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P155 : ℚ := (25865296924285929711408452886165287067762519460841 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P155 :
    phaseExp2646 phaseArg2658P155 20 =
      ((phaseValue2658P155.1,
        phaseValue2658P155.2), phaseRadius2658P155) := by
  decide +kernel

theorem phaseCosPin2658P155 :
    |Real.cos (phaseArg2658P155 : ℝ) -
      (phaseValue2658P155.1 : ℝ)| ≤
        (phaseRadius2658P155 : ℝ) := by
  have hsmall : |((phaseArg2658P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P155]
  have h := phaseExp_cos_error2646 phaseArg2658P155 20 hsmall
  rw [phaseChain2658P155] at h
  simpa [phaseValue2658P155] using h

theorem phaseSinPin2658P155 :
    |Real.sin (phaseArg2658P155 : ℝ) -
      (phaseValue2658P155.2 : ℝ)| ≤
        (phaseRadius2658P155 : ℝ) := by
  have hsmall : |((phaseArg2658P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P155]
  have h := phaseExp_sin_error2646 phaseArg2658P155 20 hsmall
  rw [phaseChain2658P155] at h
  simpa [phaseValue2658P155] using h

end ConnesWeilRH.Dev
