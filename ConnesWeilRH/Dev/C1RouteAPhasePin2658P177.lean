import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 177 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P177 : ℚ := (995075452274123102641795915346185418615228939625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P177 : RatPair2542 := ((-1060647176437824478261752816115947625494348526206691653346441673039040198620872143801364705347353 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (125050875726718665648999186172750179315160558681362259443936899784445610484088052617702789382701 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P177 : ℚ := (18540748486908653245062480750601294963607495719913 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P177 :
    phaseExp2646 phaseArg2658P177 20 =
      ((phaseValue2658P177.1,
        phaseValue2658P177.2), phaseRadius2658P177) := by
  decide +kernel

theorem phaseCosPin2658P177 :
    |Real.cos (phaseArg2658P177 : ℝ) -
      (phaseValue2658P177.1 : ℝ)| ≤
        (phaseRadius2658P177 : ℝ) := by
  have hsmall : |((phaseArg2658P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P177]
  have h := phaseExp_cos_error2646 phaseArg2658P177 20 hsmall
  rw [phaseChain2658P177] at h
  simpa [phaseValue2658P177] using h

theorem phaseSinPin2658P177 :
    |Real.sin (phaseArg2658P177 : ℝ) -
      (phaseValue2658P177.2 : ℝ)| ≤
        (phaseRadius2658P177 : ℝ) := by
  have hsmall : |((phaseArg2658P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P177]
  have h := phaseExp_sin_error2646 phaseArg2658P177 20 hsmall
  rw [phaseChain2658P177] at h
  simpa [phaseValue2658P177] using h

end ConnesWeilRH.Dev
