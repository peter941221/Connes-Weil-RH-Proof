import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 147 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P147 : ℚ := (633229833265351065317506491583936175482418416125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P147 : RatPair2542 := ((-739876610591291863921971093717376634456972720118790625603741284608843788914583190946532284650897 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2003752284770284941594074832115868326470065059209114169818728273003043492414056467830022307950325 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P147 : ℚ := (23928075039841250490556308588494550011977804116385 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P147 :
    phaseExp2646 phaseArg2658P147 20 =
      ((phaseValue2658P147.1,
        phaseValue2658P147.2), phaseRadius2658P147) := by
  decide +kernel

theorem phaseCosPin2658P147 :
    |Real.cos (phaseArg2658P147 : ℝ) -
      (phaseValue2658P147.1 : ℝ)| ≤
        (phaseRadius2658P147 : ℝ) := by
  have hsmall : |((phaseArg2658P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P147]
  have h := phaseExp_cos_error2646 phaseArg2658P147 20 hsmall
  rw [phaseChain2658P147] at h
  simpa [phaseValue2658P147] using h

theorem phaseSinPin2658P147 :
    |Real.sin (phaseArg2658P147 : ℝ) -
      (phaseValue2658P147.2 : ℝ)| ≤
        (phaseRadius2658P147 : ℝ) := by
  have hsmall : |((phaseArg2658P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P147]
  have h := phaseExp_sin_error2646 phaseArg2658P147 20 hsmall
  rw [phaseChain2658P147] at h
  simpa [phaseValue2658P147] using h

end ConnesWeilRH.Dev
