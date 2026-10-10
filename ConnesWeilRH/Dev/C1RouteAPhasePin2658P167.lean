import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 167 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P167 : ℚ := (874460245937865756867032774092102337570958765125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P167 : RatPair2542 := ((84704296942824945945345660090985207537996750498806146917844848170451614371449980605216427900967 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-2134306866338956647258961683219615989928814452186609895258023691049815140517253617736732341665857 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P167 : ℚ := (43924240871632409110044150365637552735284247116347 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P167 :
    phaseExp2646 phaseArg2658P167 20 =
      ((phaseValue2658P167.1,
        phaseValue2658P167.2), phaseRadius2658P167) := by
  decide +kernel

theorem phaseCosPin2658P167 :
    |Real.cos (phaseArg2658P167 : ℝ) -
      (phaseValue2658P167.1 : ℝ)| ≤
        (phaseRadius2658P167 : ℝ) := by
  have hsmall : |((phaseArg2658P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P167]
  have h := phaseExp_cos_error2646 phaseArg2658P167 20 hsmall
  rw [phaseChain2658P167] at h
  simpa [phaseValue2658P167] using h

theorem phaseSinPin2658P167 :
    |Real.sin (phaseArg2658P167 : ℝ) -
      (phaseValue2658P167.2 : ℝ)| ≤
        (phaseRadius2658P167 : ℝ) := by
  have hsmall : |((phaseArg2658P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P167]
  have h := phaseExp_sin_error2646 phaseArg2658P167 20 hsmall
  rw [phaseChain2658P167] at h
  simpa [phaseValue2658P167] using h

end ConnesWeilRH.Dev
