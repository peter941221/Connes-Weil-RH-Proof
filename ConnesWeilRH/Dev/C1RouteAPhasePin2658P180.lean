import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 180 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P180 : ℚ := (1031260014175000306374224857722410342928509991975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P180 : RatPair2542 := ((-2135928764204168776792132233692313177937551938830053694585633151988684853949016689251882472643683 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (15777574827824347145251636502241564387914499964280098590276515726337298930334696844809666896395 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P180 : ℚ := (43629064352977483544164396713460264126784091303433 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P180 :
    phaseExp2646 phaseArg2658P180 20 =
      ((phaseValue2658P180.1,
        phaseValue2658P180.2), phaseRadius2658P180) := by
  decide +kernel

theorem phaseCosPin2658P180 :
    |Real.cos (phaseArg2658P180 : ℝ) -
      (phaseValue2658P180.1 : ℝ)| ≤
        (phaseRadius2658P180 : ℝ) := by
  have hsmall : |((phaseArg2658P180 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P180]
  have h := phaseExp_cos_error2646 phaseArg2658P180 20 hsmall
  rw [phaseChain2658P180] at h
  simpa [phaseValue2658P180] using h

theorem phaseSinPin2658P180 :
    |Real.sin (phaseArg2658P180 : ℝ) -
      (phaseValue2658P180.2 : ℝ)| ≤
        (phaseRadius2658P180 : ℝ) := by
  have hsmall : |((phaseArg2658P180 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P180]
  have h := phaseExp_sin_error2646 phaseArg2658P180 20 hsmall
  rw [phaseChain2658P180] at h
  simpa [phaseValue2658P180] using h

end ConnesWeilRH.Dev
