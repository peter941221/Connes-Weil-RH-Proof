import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 165 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P165 : ℚ := (850337204670614287712080145841285721362104730225 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P165 : RatPair2542 := ((-226605284569537572278845222474423451186686473900199868797819830905314648145282788998077407528819 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (1129620953219426002681278622454679427354564151422647198325418483914181083403003205124475356405273 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P165 : ℚ := (36943563153503766835221569033775776317865838571515 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P165 :
    phaseExp2646 phaseArg2658P165 20 =
      ((phaseValue2658P165.1,
        phaseValue2658P165.2), phaseRadius2658P165) := by
  decide +kernel

theorem phaseCosPin2658P165 :
    |Real.cos (phaseArg2658P165 : ℝ) -
      (phaseValue2658P165.1 : ℝ)| ≤
        (phaseRadius2658P165 : ℝ) := by
  have hsmall : |((phaseArg2658P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P165]
  have h := phaseExp_cos_error2646 phaseArg2658P165 20 hsmall
  rw [phaseChain2658P165] at h
  simpa [phaseValue2658P165] using h

theorem phaseSinPin2658P165 :
    |Real.sin (phaseArg2658P165 : ℝ) -
      (phaseValue2658P165.2 : ℝ)| ≤
        (phaseRadius2658P165 : ℝ) := by
  have hsmall : |((phaseArg2658P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P165]
  have h := phaseExp_sin_error2646 phaseArg2658P165 20 hsmall
  rw [phaseChain2658P165] at h
  simpa [phaseValue2658P165] using h

end ConnesWeilRH.Dev
