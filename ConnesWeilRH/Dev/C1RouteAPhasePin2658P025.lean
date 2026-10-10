import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 025 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P025 : ℚ := (-838275684036988553134603831715877413257677712775 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P025 : RatPair2542 := ((-150048870732181437651763299774322830131736951523233434103046830875323672609501803577664464320601 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (2130710199443883152923980681929316086563847903174798384797760653633366150660855218775246420299163 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P025 : ℚ := (53301016226974866230709104987937377949138277941819 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P025 :
    phaseExp2646 phaseArg2658P025 20 =
      ((phaseValue2658P025.1,
        phaseValue2658P025.2), phaseRadius2658P025) := by
  decide +kernel

theorem phaseCosPin2658P025 :
    |Real.cos (phaseArg2658P025 : ℝ) -
      (phaseValue2658P025.1 : ℝ)| ≤
        (phaseRadius2658P025 : ℝ) := by
  have hsmall : |((phaseArg2658P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P025]
  have h := phaseExp_cos_error2646 phaseArg2658P025 20 hsmall
  rw [phaseChain2658P025] at h
  simpa [phaseValue2658P025] using h

theorem phaseSinPin2658P025 :
    |Real.sin (phaseArg2658P025 : ℝ) -
      (phaseValue2658P025.2 : ℝ)| ≤
        (phaseRadius2658P025 : ℝ) := by
  have hsmall : |((phaseArg2658P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P025]
  have h := phaseExp_sin_error2646 phaseArg2658P025 20 hsmall
  rw [phaseChain2658P025] at h
  simpa [phaseValue2658P025] using h

end ConnesWeilRH.Dev
