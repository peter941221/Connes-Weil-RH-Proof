import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 027 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P027 : ℚ := (-814152642769737083979651203465060797048823677875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P027 : RatPair2542 := ((-1677914589243803438408183829832358743203608952340919573016641796550401293652843378450140655720005 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1321757636189401254663509840208447341865168500801300489152586082042735497464448558642958281667719 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P027 : ℚ := (60946941320469005911886734028820546525136412994307 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P027 :
    phaseExp2646 phaseArg2658P027 20 =
      ((phaseValue2658P027.1,
        phaseValue2658P027.2), phaseRadius2658P027) := by
  decide +kernel

theorem phaseCosPin2658P027 :
    |Real.cos (phaseArg2658P027 : ℝ) -
      (phaseValue2658P027.1 : ℝ)| ≤
        (phaseRadius2658P027 : ℝ) := by
  have hsmall : |((phaseArg2658P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P027]
  have h := phaseExp_cos_error2646 phaseArg2658P027 20 hsmall
  rw [phaseChain2658P027] at h
  simpa [phaseValue2658P027] using h

theorem phaseSinPin2658P027 :
    |Real.sin (phaseArg2658P027 : ℝ) -
      (phaseValue2658P027.2 : ℝ)| ≤
        (phaseRadius2658P027 : ℝ) := by
  have hsmall : |((phaseArg2658P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P027]
  have h := phaseExp_sin_error2646 phaseArg2658P027 20 hsmall
  rw [phaseChain2658P027] at h
  simpa [phaseValue2658P027] using h

end ConnesWeilRH.Dev
