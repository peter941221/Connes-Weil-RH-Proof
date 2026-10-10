import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 077 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P077 : ℚ := (-211076611088450355105835497194645391827472805375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P077 : RatPair2542 := ((251261267020209710123852139749474869300151339962258829393706260094487283630791109604085091611787 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1060578662018710672365068663003065535476624305850778045744728619379806944678701107679907946368015 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P077 : ℚ := (26007402067703388096111669544559782738509133256473 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P077 :
    phaseExp2646 phaseArg2658P077 20 =
      ((phaseValue2658P077.1,
        phaseValue2658P077.2), phaseRadius2658P077) := by
  decide +kernel

theorem phaseCosPin2658P077 :
    |Real.cos (phaseArg2658P077 : ℝ) -
      (phaseValue2658P077.1 : ℝ)| ≤
        (phaseRadius2658P077 : ℝ) := by
  have hsmall : |((phaseArg2658P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P077]
  have h := phaseExp_cos_error2646 phaseArg2658P077 20 hsmall
  rw [phaseChain2658P077] at h
  simpa [phaseValue2658P077] using h

theorem phaseSinPin2658P077 :
    |Real.sin (phaseArg2658P077 : ℝ) -
      (phaseValue2658P077.2 : ℝ)| ≤
        (phaseRadius2658P077 : ℝ) := by
  have hsmall : |((phaseArg2658P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P077]
  have h := phaseExp_sin_error2646 phaseArg2658P077 20 hsmall
  rw [phaseChain2658P077] at h
  simpa [phaseValue2658P077] using h

end ConnesWeilRH.Dev
