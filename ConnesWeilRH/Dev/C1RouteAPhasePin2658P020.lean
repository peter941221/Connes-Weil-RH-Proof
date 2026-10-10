import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 020 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P020 : ℚ := (-898583287205117226021985402342918953779812800025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P020 : RatPair2542 := ((1717618990070556545238772598292058124503554537212607681277810379551078215242667999133816179537429 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1269734469316792468518083568415089702592132711252023380109243497980900772422531243210356260996315 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P020 : ℚ := (38560356815906967565935255768777122403499013509477 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P020 :
    phaseExp2646 phaseArg2658P020 20 =
      ((phaseValue2658P020.1,
        phaseValue2658P020.2), phaseRadius2658P020) := by
  decide +kernel

theorem phaseCosPin2658P020 :
    |Real.cos (phaseArg2658P020 : ℝ) -
      (phaseValue2658P020.1 : ℝ)| ≤
        (phaseRadius2658P020 : ℝ) := by
  have hsmall : |((phaseArg2658P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P020]
  have h := phaseExp_cos_error2646 phaseArg2658P020 20 hsmall
  rw [phaseChain2658P020] at h
  simpa [phaseValue2658P020] using h

theorem phaseSinPin2658P020 :
    |Real.sin (phaseArg2658P020 : ℝ) -
      (phaseValue2658P020.2 : ℝ)| ≤
        (phaseRadius2658P020 : ℝ) := by
  have hsmall : |((phaseArg2658P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P020]
  have h := phaseExp_sin_error2646 phaseArg2658P020 20 hsmall
  rw [phaseChain2658P020] at h
  simpa [phaseValue2658P020] using h

end ConnesWeilRH.Dev
