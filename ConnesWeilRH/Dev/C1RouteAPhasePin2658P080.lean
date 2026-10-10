import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 080 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P080 : ℚ := (-174892049187573151373406554818420467514191753025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P080 : RatPair2542 := ((16945124940420793451780887326956937647163543887972625711668448016177746895519044932641817431851 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1067959910338743561472189754865797206072429746101871332435218232787793872669016588191098894805067 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P080 : ℚ := (29946276834071089624792515301346752844210101338907 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P080 :
    phaseExp2646 phaseArg2658P080 20 =
      ((phaseValue2658P080.1,
        phaseValue2658P080.2), phaseRadius2658P080) := by
  decide +kernel

theorem phaseCosPin2658P080 :
    |Real.cos (phaseArg2658P080 : ℝ) -
      (phaseValue2658P080.1 : ℝ)| ≤
        (phaseRadius2658P080 : ℝ) := by
  have hsmall : |((phaseArg2658P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P080]
  have h := phaseExp_cos_error2646 phaseArg2658P080 20 hsmall
  rw [phaseChain2658P080] at h
  simpa [phaseValue2658P080] using h

theorem phaseSinPin2658P080 :
    |Real.sin (phaseArg2658P080 : ℝ) -
      (phaseValue2658P080.2 : ℝ)| ≤
        (phaseRadius2658P080 : ℝ) := by
  have hsmall : |((phaseArg2658P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P080]
  have h := phaseExp_sin_error2646 phaseArg2658P080 20 hsmall
  rw [phaseChain2658P080] at h
  simpa [phaseValue2658P080] using h

end ConnesWeilRH.Dev
