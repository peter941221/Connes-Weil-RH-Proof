import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 009 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P009 : ℚ := (-1031260014175000306374224857722410342928509991975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P009 : RatPair2542 := ((-1067964382102084388396066116846156588968775969415026847292816575994342426974508344625941236325779 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-15777574827824347145251636502241564387914499964280098590276515726337298930334696844809664800999 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P009 : ℚ := (43629064352977483544164396713460264126784091303433 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P009 :
    phaseExp2646 phaseArg2658P009 20 =
      ((phaseValue2658P009.1,
        phaseValue2658P009.2), phaseRadius2658P009) := by
  decide +kernel

theorem phaseCosPin2658P009 :
    |Real.cos (phaseArg2658P009 : ℝ) -
      (phaseValue2658P009.1 : ℝ)| ≤
        (phaseRadius2658P009 : ℝ) := by
  have hsmall : |((phaseArg2658P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P009]
  have h := phaseExp_cos_error2646 phaseArg2658P009 20 hsmall
  rw [phaseChain2658P009] at h
  simpa [phaseValue2658P009] using h

theorem phaseSinPin2658P009 :
    |Real.sin (phaseArg2658P009 : ℝ) -
      (phaseValue2658P009.2 : ℝ)| ≤
        (phaseRadius2658P009 : ℝ) := by
  have hsmall : |((phaseArg2658P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P009]
  have h := phaseExp_sin_error2646 phaseArg2658P009 20 hsmall
  rw [phaseChain2658P009] at h
  simpa [phaseValue2658P009] using h

end ConnesWeilRH.Dev
