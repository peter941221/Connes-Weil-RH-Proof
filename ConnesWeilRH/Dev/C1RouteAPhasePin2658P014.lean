import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 014 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P014 : ℚ := (-970952411006871633486843287095368802406374904725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P014 : RatPair2542 := ((87451014963975272046416218449474396629744892549088851342762323197949346557032248179189772760523 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-806944008738441207426272038086973822557931360857295622051666520793052384578126855554668534710401 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P014 : ℚ := (23434136269616166454103511248654309025770157817795 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P014 :
    phaseExp2646 phaseArg2658P014 20 =
      ((phaseValue2658P014.1,
        phaseValue2658P014.2), phaseRadius2658P014) := by
  decide +kernel

theorem phaseCosPin2658P014 :
    |Real.cos (phaseArg2658P014 : ℝ) -
      (phaseValue2658P014.1 : ℝ)| ≤
        (phaseRadius2658P014 : ℝ) := by
  have hsmall : |((phaseArg2658P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P014]
  have h := phaseExp_cos_error2646 phaseArg2658P014 20 hsmall
  rw [phaseChain2658P014] at h
  simpa [phaseValue2658P014] using h

theorem phaseSinPin2658P014 :
    |Real.sin (phaseArg2658P014 : ℝ) -
      (phaseValue2658P014.2 : ℝ)| ≤
        (phaseRadius2658P014 : ℝ) := by
  have hsmall : |((phaseArg2658P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P014]
  have h := phaseExp_sin_error2646 phaseArg2658P014 20 hsmall
  rw [phaseChain2658P014] at h
  simpa [phaseValue2658P014] using h

end ConnesWeilRH.Dev
