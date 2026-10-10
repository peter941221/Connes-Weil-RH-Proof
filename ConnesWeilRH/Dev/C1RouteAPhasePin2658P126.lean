import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 126 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P126 : ℚ := (379937899959210639190503894950361705289451049675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P126 : RatPair2542 := ((431668141389844195814823313254909100032185123942481862827745110754009068770874175309951849548249 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (1953737720488178817446064608110644932419256911503774124047647588332799092143306994258704112649749 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P126 : ℚ := (1485463589907095487828727682969637703583751253035 / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168)

theorem phaseChain2658P126 :
    phaseExp2646 phaseArg2658P126 20 =
      ((phaseValue2658P126.1,
        phaseValue2658P126.2), phaseRadius2658P126) := by
  decide +kernel

theorem phaseCosPin2658P126 :
    |Real.cos (phaseArg2658P126 : ℝ) -
      (phaseValue2658P126.1 : ℝ)| ≤
        (phaseRadius2658P126 : ℝ) := by
  have hsmall : |((phaseArg2658P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P126]
  have h := phaseExp_cos_error2646 phaseArg2658P126 20 hsmall
  rw [phaseChain2658P126] at h
  simpa [phaseValue2658P126] using h

theorem phaseSinPin2658P126 :
    |Real.sin (phaseArg2658P126 : ℝ) -
      (phaseValue2658P126.2 : ℝ)| ≤
        (phaseRadius2658P126 : ℝ) := by
  have hsmall : |((phaseArg2658P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P126]
  have h := phaseExp_sin_error2646 phaseArg2658P126 20 hsmall
  rw [phaseChain2658P126] at h
  simpa [phaseValue2658P126] using h

end ConnesWeilRH.Dev
