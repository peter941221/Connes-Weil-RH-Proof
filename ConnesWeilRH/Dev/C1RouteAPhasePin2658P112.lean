import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 112 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P112 : ℚ := (211076611088450355105835497194645391827472805375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P112 : RatPair2542 := ((251261267020209710123852139749474869300151339962258829393706260094487283630791109604085089529947 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-530289331009355336182534331501532767738312152925389022872364309689903472339350553839953973245059 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P112 : ℚ := (26007402067703388096111669544559782738509133256473 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P112 :
    phaseExp2646 phaseArg2658P112 20 =
      ((phaseValue2658P112.1,
        phaseValue2658P112.2), phaseRadius2658P112) := by
  decide +kernel

theorem phaseCosPin2658P112 :
    |Real.cos (phaseArg2658P112 : ℝ) -
      (phaseValue2658P112.1 : ℝ)| ≤
        (phaseRadius2658P112 : ℝ) := by
  have hsmall : |((phaseArg2658P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P112]
  have h := phaseExp_cos_error2646 phaseArg2658P112 20 hsmall
  rw [phaseChain2658P112] at h
  simpa [phaseValue2658P112] using h

theorem phaseSinPin2658P112 :
    |Real.sin (phaseArg2658P112 : ℝ) -
      (phaseValue2658P112.2 : ℝ)| ≤
        (phaseRadius2658P112 : ℝ) := by
  have hsmall : |((phaseArg2658P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P112]
  have h := phaseExp_sin_error2646 phaseArg2658P112 20 hsmall
  rw [phaseChain2658P112] at h
  simpa [phaseValue2658P112] using h

end ConnesWeilRH.Dev
