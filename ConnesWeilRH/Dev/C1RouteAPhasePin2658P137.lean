import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 137 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P137 : ℚ := (512614626929093719542743350329853094438148241625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P137 : RatPair2542 := ((-1863397644436452578452361392584606490172459742374762766451469352303483921053098539757966096674309 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-522060781023358205880242984335901437905192927126703177905161171456329665407166387794034119314653 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P137 : ℚ := (37975673490378908897171574868058978886820828213971 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P137 :
    phaseExp2646 phaseArg2658P137 20 =
      ((phaseValue2658P137.1,
        phaseValue2658P137.2), phaseRadius2658P137) := by
  decide +kernel

theorem phaseCosPin2658P137 :
    |Real.cos (phaseArg2658P137 : ℝ) -
      (phaseValue2658P137.1 : ℝ)| ≤
        (phaseRadius2658P137 : ℝ) := by
  have hsmall : |((phaseArg2658P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P137]
  have h := phaseExp_cos_error2646 phaseArg2658P137 20 hsmall
  rw [phaseChain2658P137] at h
  simpa [phaseValue2658P137] using h

theorem phaseSinPin2658P137 :
    |Real.sin (phaseArg2658P137 : ℝ) -
      (phaseValue2658P137.2 : ℝ)| ≤
        (phaseRadius2658P137 : ℝ) := by
  have hsmall : |((phaseArg2658P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P137]
  have h := phaseExp_sin_error2646 phaseArg2658P137 20 hsmall
  rw [phaseChain2658P137] at h
  simpa [phaseValue2658P137] using h

end ConnesWeilRH.Dev
