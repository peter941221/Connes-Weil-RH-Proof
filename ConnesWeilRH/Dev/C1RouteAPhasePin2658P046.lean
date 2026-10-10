import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 046 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P046 : ℚ := (-584983750730848127007601235082302943064710346325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P046 : RatPair2542 := ((-1590706180897789117391732947494369178177605539280796953982513090761222339063214282585772812302925 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (712757754022319532543732154768596960226137239823559781186569474895870639872233331845402834639721 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P046 : ℚ := (25420406021232466503957081951951850841566968099019 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P046 :
    phaseExp2646 phaseArg2658P046 20 =
      ((phaseValue2658P046.1,
        phaseValue2658P046.2), phaseRadius2658P046) := by
  decide +kernel

theorem phaseCosPin2658P046 :
    |Real.cos (phaseArg2658P046 : ℝ) -
      (phaseValue2658P046.1 : ℝ)| ≤
        (phaseRadius2658P046 : ℝ) := by
  have hsmall : |((phaseArg2658P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P046]
  have h := phaseExp_cos_error2646 phaseArg2658P046 20 hsmall
  rw [phaseChain2658P046] at h
  simpa [phaseValue2658P046] using h

theorem phaseSinPin2658P046 :
    |Real.sin (phaseArg2658P046 : ℝ) -
      (phaseValue2658P046.2 : ℝ)| ≤
        (phaseRadius2658P046 : ℝ) := by
  have hsmall : |((phaseArg2658P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P046]
  have h := phaseExp_sin_error2646 phaseArg2658P046 20 hsmall
  rw [phaseChain2658P046] at h
  simpa [phaseValue2658P046] using h

end ConnesWeilRH.Dev
