import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 056 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P056 : ℚ := (-464368544394590781232838093828219862020440171825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P056 : RatPair2542 := ((414183155711033096774488950152789791677768823221830795143575265571515119334177347135727288800749 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (337053188868815351839527373468525510824154572838561573732511898227424444311305156070364719708901 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P056 : ℚ := (16156607629150550461453658580058898686847583627269 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P056 :
    phaseExp2646 phaseArg2658P056 20 =
      ((phaseValue2658P056.1,
        phaseValue2658P056.2), phaseRadius2658P056) := by
  decide +kernel

theorem phaseCosPin2658P056 :
    |Real.cos (phaseArg2658P056 : ℝ) -
      (phaseValue2658P056.1 : ℝ)| ≤
        (phaseRadius2658P056 : ℝ) := by
  have hsmall : |((phaseArg2658P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P056]
  have h := phaseExp_cos_error2646 phaseArg2658P056 20 hsmall
  rw [phaseChain2658P056] at h
  simpa [phaseValue2658P056] using h

theorem phaseSinPin2658P056 :
    |Real.sin (phaseArg2658P056 : ℝ) -
      (phaseValue2658P056.2 : ℝ)| ≤
        (phaseRadius2658P056 : ℝ) := by
  have hsmall : |((phaseArg2658P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P056]
  have h := phaseExp_sin_error2646 phaseArg2658P056 20 hsmall
  rw [phaseChain2658P056] at h
  simpa [phaseValue2658P056] using h

end ConnesWeilRH.Dev
