import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 052 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P052 : ℚ := (-512614626929093719542743350329853094438148241625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P052 : RatPair2542 := ((-1863397644436452578452361392584606490172459742374762766451469352303483921053098539757966095672223 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (16314399406979943933757593260496919934537278972709474309536286608010302043973949618563566257277 / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384))
def phaseRadius2658P052 : ℚ := (37975673490378908897171574868058978886820828213971 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P052 :
    phaseExp2646 phaseArg2658P052 20 =
      ((phaseValue2658P052.1,
        phaseValue2658P052.2), phaseRadius2658P052) := by
  decide +kernel

theorem phaseCosPin2658P052 :
    |Real.cos (phaseArg2658P052 : ℝ) -
      (phaseValue2658P052.1 : ℝ)| ≤
        (phaseRadius2658P052 : ℝ) := by
  have hsmall : |((phaseArg2658P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P052]
  have h := phaseExp_cos_error2646 phaseArg2658P052 20 hsmall
  rw [phaseChain2658P052] at h
  simpa [phaseValue2658P052] using h

theorem phaseSinPin2658P052 :
    |Real.sin (phaseArg2658P052 : ℝ) -
      (phaseValue2658P052.2 : ℝ)| ≤
        (phaseRadius2658P052 : ℝ) := by
  have hsmall : |((phaseArg2658P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P052]
  have h := phaseExp_sin_error2646 phaseArg2658P052 20 hsmall
  rw [phaseChain2658P052] at h
  simpa [phaseValue2658P052] using h

end ConnesWeilRH.Dev
