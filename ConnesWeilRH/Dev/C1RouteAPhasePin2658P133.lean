import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 133 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P133 : ℚ := (464368544394590781232838093828219862020440171825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P133 : RatPair2542 := ((828366311422066193548977900305579583355537646443661590287150531143030238668354694271454576938809 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-337053188868815351839527373468525510824154572838561573732511898227424444311305156070364720115207 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P133 : ℚ := (16156607629150550461453658580058898686847583627269 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P133 :
    phaseExp2646 phaseArg2658P133 20 =
      ((phaseValue2658P133.1,
        phaseValue2658P133.2), phaseRadius2658P133) := by
  decide +kernel

theorem phaseCosPin2658P133 :
    |Real.cos (phaseArg2658P133 : ℝ) -
      (phaseValue2658P133.1 : ℝ)| ≤
        (phaseRadius2658P133 : ℝ) := by
  have hsmall : |((phaseArg2658P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P133]
  have h := phaseExp_cos_error2646 phaseArg2658P133 20 hsmall
  rw [phaseChain2658P133] at h
  simpa [phaseValue2658P133] using h

theorem phaseSinPin2658P133 :
    |Real.sin (phaseArg2658P133 : ℝ) -
      (phaseValue2658P133.2 : ℝ)| ≤
        (phaseRadius2658P133 : ℝ) := by
  have hsmall : |((phaseArg2658P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P133]
  have h := phaseExp_sin_error2646 phaseArg2658P133 20 hsmall
  rw [phaseChain2658P133] at h
  simpa [phaseValue2658P133] using h

end ConnesWeilRH.Dev
