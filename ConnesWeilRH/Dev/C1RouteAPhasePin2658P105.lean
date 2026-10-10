import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 105 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P105 : ℚ := (126645966653070213063501298316787235096483683225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P105 : RatPair2542 := ((1979707644601691045498621729369852650094952762644222823577262350313286021850416606648012506341365 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (200499105286005540518872628812855823408830377839700201578978986556043125130368036905242183731975 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P105 : ℚ := (18150489506829354780149710589362566392987030463351 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P105 :
    phaseExp2646 phaseArg2658P105 20 =
      ((phaseValue2658P105.1,
        phaseValue2658P105.2), phaseRadius2658P105) := by
  decide +kernel

theorem phaseCosPin2658P105 :
    |Real.cos (phaseArg2658P105 : ℝ) -
      (phaseValue2658P105.1 : ℝ)| ≤
        (phaseRadius2658P105 : ℝ) := by
  have hsmall : |((phaseArg2658P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P105]
  have h := phaseExp_cos_error2646 phaseArg2658P105 20 hsmall
  rw [phaseChain2658P105] at h
  simpa [phaseValue2658P105] using h

theorem phaseSinPin2658P105 :
    |Real.sin (phaseArg2658P105 : ℝ) -
      (phaseValue2658P105.2 : ℝ)| ≤
        (phaseRadius2658P105 : ℝ) := by
  have hsmall : |((phaseArg2658P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P105]
  have h := phaseExp_sin_error2646 phaseArg2658P105 20 hsmall
  rw [phaseChain2658P105] at h
  simpa [phaseValue2658P105] using h

end ConnesWeilRH.Dev
