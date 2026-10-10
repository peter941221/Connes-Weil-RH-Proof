import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 116 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P116 : ℚ := (259322693622953293415740753696278624245180875175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P116 : RatPair2542 := ((-2064709609055201927034065129533229423148459759947984048475386859030076172321577864256269882862493 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (547188128432361404491295617345844885291007853356855358796823217964912124908986734698169992046693 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P116 : ℚ := (27246057361055028439744327953986621842357604755141 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P116 :
    phaseExp2646 phaseArg2658P116 20 =
      ((phaseValue2658P116.1,
        phaseValue2658P116.2), phaseRadius2658P116) := by
  decide +kernel

theorem phaseCosPin2658P116 :
    |Real.cos (phaseArg2658P116 : ℝ) -
      (phaseValue2658P116.1 : ℝ)| ≤
        (phaseRadius2658P116 : ℝ) := by
  have hsmall : |((phaseArg2658P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P116]
  have h := phaseExp_cos_error2646 phaseArg2658P116 20 hsmall
  rw [phaseChain2658P116] at h
  simpa [phaseValue2658P116] using h

theorem phaseSinPin2658P116 :
    |Real.sin (phaseArg2658P116 : ℝ) -
      (phaseValue2658P116.2 : ℝ)| ≤
        (phaseRadius2658P116 : ℝ) := by
  have hsmall : |((phaseArg2658P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P116]
  have h := phaseExp_sin_error2646 phaseArg2658P116 20 hsmall
  rw [phaseChain2658P116] at h
  simpa [phaseValue2658P116] using h

end ConnesWeilRH.Dev
