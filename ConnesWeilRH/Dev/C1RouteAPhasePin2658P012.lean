import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 012 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P012 : ℚ := (-995075452274123102641795915346185418615228939625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P012 : RatPair2542 := ((-1060647176437824478261752816115947625494348526206691653346441673039040198620872143801364705467313 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-62525437863359332824499593086375089657580279340681129721968449892222805242044026308851394177171 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P012 : ℚ := (18540748486908653245062480750601294963607495719913 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P012 :
    phaseExp2646 phaseArg2658P012 20 =
      ((phaseValue2658P012.1,
        phaseValue2658P012.2), phaseRadius2658P012) := by
  decide +kernel

theorem phaseCosPin2658P012 :
    |Real.cos (phaseArg2658P012 : ℝ) -
      (phaseValue2658P012.1 : ℝ)| ≤
        (phaseRadius2658P012 : ℝ) := by
  have hsmall : |((phaseArg2658P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P012]
  have h := phaseExp_cos_error2646 phaseArg2658P012 20 hsmall
  rw [phaseChain2658P012] at h
  simpa [phaseValue2658P012] using h

theorem phaseSinPin2658P012 :
    |Real.sin (phaseArg2658P012 : ℝ) -
      (phaseValue2658P012.2 : ℝ)| ≤
        (phaseRadius2658P012 : ℝ) := by
  have hsmall : |((phaseArg2658P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P012]
  have h := phaseExp_sin_error2646 phaseArg2658P012 20 hsmall
  rw [phaseChain2658P012] at h
  simpa [phaseValue2658P012] using h

end ConnesWeilRH.Dev
