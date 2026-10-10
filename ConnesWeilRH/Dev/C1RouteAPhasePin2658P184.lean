import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 184 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P184 : ℚ := (1079506096709503244684130114224043575346218061775 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P184 : RatPair2542 := ((50057133953485520917941918125929029014333384032581247371842126519469734508202123741085508611399 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (1980145740281526302284101653054735980715699167245348113343375957435017309887378952010618898772161 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P184 : ℚ := (16894524102764441207551027875489187366683893140049 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P184 :
    phaseExp2646 phaseArg2658P184 20 =
      ((phaseValue2658P184.1,
        phaseValue2658P184.2), phaseRadius2658P184) := by
  decide +kernel

theorem phaseCosPin2658P184 :
    |Real.cos (phaseArg2658P184 : ℝ) -
      (phaseValue2658P184.1 : ℝ)| ≤
        (phaseRadius2658P184 : ℝ) := by
  have hsmall : |((phaseArg2658P184 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P184]
  have h := phaseExp_cos_error2646 phaseArg2658P184 20 hsmall
  rw [phaseChain2658P184] at h
  simpa [phaseValue2658P184] using h

theorem phaseSinPin2658P184 :
    |Real.sin (phaseArg2658P184 : ℝ) -
      (phaseValue2658P184.2 : ℝ)| ≤
        (phaseRadius2658P184 : ℝ) := by
  have hsmall : |((phaseArg2658P184 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P184]
  have h := phaseExp_sin_error2646 phaseArg2658P184 20 hsmall
  rw [phaseChain2658P184] at h
  simpa [phaseValue2658P184] using h

end ConnesWeilRH.Dev
