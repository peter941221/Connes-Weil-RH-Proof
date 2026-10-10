import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 084 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P084 : ℚ := (-126645966653070213063501298316787235096483683225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P084 : RatPair2542 := ((989853822300845522749310864684926325047476381322111411788631175156643010925208303324006252782105 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-801996421144022162075490515251423293635321511358800806315915946224172500521472147620968736875977 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P084 : ℚ := (18150489506829354780149710589362566392987030463351 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P084 :
    phaseExp2646 phaseArg2658P084 20 =
      ((phaseValue2658P084.1,
        phaseValue2658P084.2), phaseRadius2658P084) := by
  decide +kernel

theorem phaseCosPin2658P084 :
    |Real.cos (phaseArg2658P084 : ℝ) -
      (phaseValue2658P084.1 : ℝ)| ≤
        (phaseRadius2658P084 : ℝ) := by
  have hsmall : |((phaseArg2658P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P084]
  have h := phaseExp_cos_error2646 phaseArg2658P084 20 hsmall
  rw [phaseChain2658P084] at h
  simpa [phaseValue2658P084] using h

theorem phaseSinPin2658P084 :
    |Real.sin (phaseArg2658P084 : ℝ) -
      (phaseValue2658P084.2 : ℝ)| ≤
        (phaseRadius2658P084 : ℝ) := by
  have hsmall : |((phaseArg2658P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P084]
  have h := phaseExp_sin_error2646 phaseArg2658P084 20 hsmall
  rw [phaseChain2658P084] at h
  simpa [phaseValue2658P084] using h

end ConnesWeilRH.Dev
