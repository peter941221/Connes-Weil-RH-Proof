import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 143 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P143 : ℚ := (584983750730848127007601235082302943064710346325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P143 : RatPair2542 := ((-795353090448894558695866473747184589088802769640398476991256545380611169531607141292886406847297 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-1425515508044639065087464309537193920452274479647119562373138949791741279744466663690805667710097 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P143 : ℚ := (25420406021232466503957081951951850841566968099019 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P143 :
    phaseExp2646 phaseArg2658P143 20 =
      ((phaseValue2658P143.1,
        phaseValue2658P143.2), phaseRadius2658P143) := by
  decide +kernel

theorem phaseCosPin2658P143 :
    |Real.cos (phaseArg2658P143 : ℝ) -
      (phaseValue2658P143.1 : ℝ)| ≤
        (phaseRadius2658P143 : ℝ) := by
  have hsmall : |((phaseArg2658P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P143]
  have h := phaseExp_cos_error2646 phaseArg2658P143 20 hsmall
  rw [phaseChain2658P143] at h
  simpa [phaseValue2658P143] using h

theorem phaseSinPin2658P143 :
    |Real.sin (phaseArg2658P143 : ℝ) -
      (phaseValue2658P143.2 : ℝ)| ≤
        (phaseRadius2658P143 : ℝ) := by
  have hsmall : |((phaseArg2658P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P143]
  have h := phaseExp_sin_error2646 phaseArg2658P143 20 hsmall
  rw [phaseChain2658P143] at h
  simpa [phaseValue2658P143] using h

end ConnesWeilRH.Dev
