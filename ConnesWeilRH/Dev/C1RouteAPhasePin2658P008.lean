import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 008 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P008 : ℚ := (-1043321534808626040951701171847818651032937009425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P008 : RatPair2542 := ((1013398150179995201162494922485216798690833308510012423265486824666933056001888547968546520244087 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-470070792995185401180260499069140974260919308560868578837602364334936739410086101719308513231127 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P008 : ℚ := (46508343479931024329658485266003149359771727559623 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P008 :
    phaseExp2646 phaseArg2658P008 20 =
      ((phaseValue2658P008.1,
        phaseValue2658P008.2), phaseRadius2658P008) := by
  decide +kernel

theorem phaseCosPin2658P008 :
    |Real.cos (phaseArg2658P008 : ℝ) -
      (phaseValue2658P008.1 : ℝ)| ≤
        (phaseRadius2658P008 : ℝ) := by
  have hsmall : |((phaseArg2658P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P008]
  have h := phaseExp_cos_error2646 phaseArg2658P008 20 hsmall
  rw [phaseChain2658P008] at h
  simpa [phaseValue2658P008] using h

theorem phaseSinPin2658P008 :
    |Real.sin (phaseArg2658P008 : ℝ) -
      (phaseValue2658P008.2 : ℝ)| ≤
        (phaseRadius2658P008 : ℝ) := by
  have hsmall : |((phaseArg2658P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P008]
  have h := phaseExp_sin_error2646 phaseArg2658P008 20 hsmall
  rw [phaseChain2658P008] at h
  simpa [phaseValue2658P008] using h

end ConnesWeilRH.Dev
