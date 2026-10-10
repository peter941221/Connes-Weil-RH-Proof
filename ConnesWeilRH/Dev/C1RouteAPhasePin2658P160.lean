import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 160 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P160 : ℚ := (790029601502485614824698575214244180839969642975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P160 : RatPair2542 := ((1018167507186996866975449584628678583346002249098402519751333260805931875233194707560765499557165 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (322405151500663040964028091796765965474925457416576319931599584313760213458444189311103322463773 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P160 : ℚ := (26252280883971115827062905526400807627448884065573 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P160 :
    phaseExp2646 phaseArg2658P160 20 =
      ((phaseValue2658P160.1,
        phaseValue2658P160.2), phaseRadius2658P160) := by
  decide +kernel

theorem phaseCosPin2658P160 :
    |Real.cos (phaseArg2658P160 : ℝ) -
      (phaseValue2658P160.1 : ℝ)| ≤
        (phaseRadius2658P160 : ℝ) := by
  have hsmall : |((phaseArg2658P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P160]
  have h := phaseExp_cos_error2646 phaseArg2658P160 20 hsmall
  rw [phaseChain2658P160] at h
  simpa [phaseValue2658P160] using h

theorem phaseSinPin2658P160 :
    |Real.sin (phaseArg2658P160 : ℝ) -
      (phaseValue2658P160.2 : ℝ)| ≤
        (phaseRadius2658P160 : ℝ) := by
  have hsmall : |((phaseArg2658P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P160]
  have h := phaseExp_sin_error2646 phaseArg2658P160 20 hsmall
  rw [phaseChain2658P160] at h
  simpa [phaseValue2658P160] using h

end ConnesWeilRH.Dev
