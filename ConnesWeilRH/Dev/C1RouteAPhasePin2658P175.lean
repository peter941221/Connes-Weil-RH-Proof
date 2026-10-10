import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 175 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P175 : ℚ := (970952411006871633486843287095368802406374904725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P175 : RatPair2542 := ((1399216239423604352742659495191590346075918280785421621484197171167189544912515970867036365771181 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (806944008738441207426272038086973822557931360857295622051666520793052384578126855554668534032833 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P175 : ℚ := (23434136269616166454103511248654309025770157817795 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P175 :
    phaseExp2646 phaseArg2658P175 20 =
      ((phaseValue2658P175.1,
        phaseValue2658P175.2), phaseRadius2658P175) := by
  decide +kernel

theorem phaseCosPin2658P175 :
    |Real.cos (phaseArg2658P175 : ℝ) -
      (phaseValue2658P175.1 : ℝ)| ≤
        (phaseRadius2658P175 : ℝ) := by
  have hsmall : |((phaseArg2658P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P175]
  have h := phaseExp_cos_error2646 phaseArg2658P175 20 hsmall
  rw [phaseChain2658P175] at h
  simpa [phaseValue2658P175] using h

theorem phaseSinPin2658P175 :
    |Real.sin (phaseArg2658P175 : ℝ) -
      (phaseValue2658P175.2 : ℝ)| ≤
        (phaseRadius2658P175 : ℝ) := by
  have hsmall : |((phaseArg2658P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P175]
  have h := phaseExp_sin_error2646 phaseArg2658P175 20 hsmall
  rw [phaseChain2658P175] at h
  simpa [phaseValue2658P175] using h

end ConnesWeilRH.Dev
