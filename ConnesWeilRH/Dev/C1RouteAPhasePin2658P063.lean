import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 063 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P063 : ℚ := (-379937899959210639190503894950361705289451049675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P063 : RatPair2542 := ((215834070694922097907411656627454550016092561971240931413872555377004534385437087654975924295023 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (-488434430122044704361516152027661233104814227875943531011911897083199773035826748564676028375151 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P063 : ℚ := (1485463589907095487828727682969637703583751253035 / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168)

theorem phaseChain2658P063 :
    phaseExp2646 phaseArg2658P063 20 =
      ((phaseValue2658P063.1,
        phaseValue2658P063.2), phaseRadius2658P063) := by
  decide +kernel

theorem phaseCosPin2658P063 :
    |Real.cos (phaseArg2658P063 : ℝ) -
      (phaseValue2658P063.1 : ℝ)| ≤
        (phaseRadius2658P063 : ℝ) := by
  have hsmall : |((phaseArg2658P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P063]
  have h := phaseExp_cos_error2646 phaseArg2658P063 20 hsmall
  rw [phaseChain2658P063] at h
  simpa [phaseValue2658P063] using h

theorem phaseSinPin2658P063 :
    |Real.sin (phaseArg2658P063 : ℝ) -
      (phaseValue2658P063.2 : ℝ)| ≤
        (phaseRadius2658P063 : ℝ) := by
  have hsmall : |((phaseArg2658P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P063]
  have h := phaseExp_sin_error2646 phaseArg2658P063 20 hsmall
  rw [phaseChain2658P063] at h
  simpa [phaseValue2658P063] using h

end ConnesWeilRH.Dev
