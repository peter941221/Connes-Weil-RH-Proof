import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 170 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P170 : ℚ := (910644807838742960599461716468327261884239817475 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P170 : RatPair2542 := ((318434093698615292638808399407473139927549068970541345928591233853747736657753321206348001963459 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-528029375697539714719551869290104695060428833477899503091183499380713864754881576571679587513515 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P170 : ℚ := (64434626149014444608444449341741487277254221573221 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P170 :
    phaseExp2646 phaseArg2658P170 20 =
      ((phaseValue2658P170.1,
        phaseValue2658P170.2), phaseRadius2658P170) := by
  decide +kernel

theorem phaseCosPin2658P170 :
    |Real.cos (phaseArg2658P170 : ℝ) -
      (phaseValue2658P170.1 : ℝ)| ≤
        (phaseRadius2658P170 : ℝ) := by
  have hsmall : |((phaseArg2658P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P170]
  have h := phaseExp_cos_error2646 phaseArg2658P170 20 hsmall
  rw [phaseChain2658P170] at h
  simpa [phaseValue2658P170] using h

theorem phaseSinPin2658P170 :
    |Real.sin (phaseArg2658P170 : ℝ) -
      (phaseValue2658P170.2 : ℝ)| ≤
        (phaseRadius2658P170 : ℝ) := by
  have hsmall : |((phaseArg2658P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P170]
  have h := phaseExp_sin_error2646 phaseArg2658P170 20 hsmall
  rw [phaseChain2658P170] at h
  simpa [phaseValue2658P170] using h

end ConnesWeilRH.Dev
