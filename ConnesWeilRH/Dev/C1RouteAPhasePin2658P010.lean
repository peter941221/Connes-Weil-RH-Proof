import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 010 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P010 : ℚ := (-1019198493541374571796748543597002034824082974525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P010 : RatPair2542 := ((123188839093747094144612153239686003467683865052011088256085461622149359155406789975414672245927 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (473762153714632160708743101616741241794191130087420758335576232486530214825812063809586350560657 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P010 : ℚ := (48313005605203001411019011731067113760122242023187 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P010 :
    phaseExp2646 phaseArg2658P010 20 =
      ((phaseValue2658P010.1,
        phaseValue2658P010.2), phaseRadius2658P010) := by
  decide +kernel

theorem phaseCosPin2658P010 :
    |Real.cos (phaseArg2658P010 : ℝ) -
      (phaseValue2658P010.1 : ℝ)| ≤
        (phaseRadius2658P010 : ℝ) := by
  have hsmall : |((phaseArg2658P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P010]
  have h := phaseExp_cos_error2646 phaseArg2658P010 20 hsmall
  rw [phaseChain2658P010] at h
  simpa [phaseValue2658P010] using h

theorem phaseSinPin2658P010 :
    |Real.sin (phaseArg2658P010 : ℝ) -
      (phaseValue2658P010.2 : ℝ)| ≤
        (phaseRadius2658P010 : ℝ) := by
  have hsmall : |((phaseArg2658P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P010]
  have h := phaseExp_sin_error2646 phaseArg2658P010 20 hsmall
  rw [phaseChain2658P010] at h
  simpa [phaseValue2658P010] using h

end ConnesWeilRH.Dev
