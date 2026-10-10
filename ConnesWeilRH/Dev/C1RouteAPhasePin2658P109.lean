import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 109 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P109 : ℚ := (174892049187573151373406554818420467514191753025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P109 : RatPair2542 := ((16945124940420793451780887326956937647163543887972625711668448016177746895519044932641815335965 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-2135919820677487122944379509731594412144859492203742664870436465575587745338033176382197789629269 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P109 : ℚ := (29946276834071089624792515301346752844210101338907 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P109 :
    phaseExp2646 phaseArg2658P109 20 =
      ((phaseValue2658P109.1,
        phaseValue2658P109.2), phaseRadius2658P109) := by
  decide +kernel

theorem phaseCosPin2658P109 :
    |Real.cos (phaseArg2658P109 : ℝ) -
      (phaseValue2658P109.1 : ℝ)| ≤
        (phaseRadius2658P109 : ℝ) := by
  have hsmall : |((phaseArg2658P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P109]
  have h := phaseExp_cos_error2646 phaseArg2658P109 20 hsmall
  rw [phaseChain2658P109] at h
  simpa [phaseValue2658P109] using h

theorem phaseSinPin2658P109 :
    |Real.sin (phaseArg2658P109 : ℝ) -
      (phaseValue2658P109.2 : ℝ)| ≤
        (phaseRadius2658P109 : ℝ) := by
  have hsmall : |((phaseArg2658P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P109]
  have h := phaseExp_sin_error2646 phaseArg2658P109 20 hsmall
  rw [phaseChain2658P109] at h
  simpa [phaseValue2658P109] using h

end ConnesWeilRH.Dev
