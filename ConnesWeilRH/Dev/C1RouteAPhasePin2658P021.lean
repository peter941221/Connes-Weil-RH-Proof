import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 021 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P021 : ℚ := (-886521766571491491444509088217510645675385782575 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P021 : RatPair2542 := ((-962933884210245776693178897486191258082490170508799176317328617942707692051929718823256751337065 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-461918270958529831484898089043821201723451471977462324908042479399254533740029614341016783911153 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P021 : ℚ := (48841857627748226282879193415656480139583728384343 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P021 :
    phaseExp2646 phaseArg2658P021 20 =
      ((phaseValue2658P021.1,
        phaseValue2658P021.2), phaseRadius2658P021) := by
  decide +kernel

theorem phaseCosPin2658P021 :
    |Real.cos (phaseArg2658P021 : ℝ) -
      (phaseValue2658P021.1 : ℝ)| ≤
        (phaseRadius2658P021 : ℝ) := by
  have hsmall : |((phaseArg2658P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P021]
  have h := phaseExp_cos_error2646 phaseArg2658P021 20 hsmall
  rw [phaseChain2658P021] at h
  simpa [phaseValue2658P021] using h

theorem phaseSinPin2658P021 :
    |Real.sin (phaseArg2658P021 : ℝ) -
      (phaseValue2658P021.2 : ℝ)| ≤
        (phaseRadius2658P021 : ℝ) := by
  have hsmall : |((phaseArg2658P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P021]
  have h := phaseExp_sin_error2646 phaseArg2658P021 20 hsmall
  rw [phaseChain2658P021] at h
  simpa [phaseValue2658P021] using h

end ConnesWeilRH.Dev
