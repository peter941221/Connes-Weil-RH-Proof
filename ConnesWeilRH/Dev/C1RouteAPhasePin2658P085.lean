import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 085 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P085 : ℚ := (-114584446019444478486024984191378926992056665775 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P085 : RatPair2542 := ((-817566795244161747173521727178560052553467060951910804774656776662848635115295366190961265200349 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-85895529725771718398727662656257450494666465716480145212086853177164764192686264409932912728645 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536))
def phaseRadius2658P085 : ℚ := (24971821524039761577970586939247419364437649558533 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P085 :
    phaseExp2646 phaseArg2658P085 20 =
      ((phaseValue2658P085.1,
        phaseValue2658P085.2), phaseRadius2658P085) := by
  decide +kernel

theorem phaseCosPin2658P085 :
    |Real.cos (phaseArg2658P085 : ℝ) -
      (phaseValue2658P085.1 : ℝ)| ≤
        (phaseRadius2658P085 : ℝ) := by
  have hsmall : |((phaseArg2658P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P085]
  have h := phaseExp_cos_error2646 phaseArg2658P085 20 hsmall
  rw [phaseChain2658P085] at h
  simpa [phaseValue2658P085] using h

theorem phaseSinPin2658P085 :
    |Real.sin (phaseArg2658P085 : ℝ) -
      (phaseValue2658P085.2 : ℝ)| ≤
        (phaseRadius2658P085 : ℝ) := by
  have hsmall : |((phaseArg2658P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P085]
  have h := phaseExp_sin_error2646 phaseArg2658P085 20 hsmall
  rw [phaseChain2658P085] at h
  simpa [phaseValue2658P085] using h

end ConnesWeilRH.Dev
