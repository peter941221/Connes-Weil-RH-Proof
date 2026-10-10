import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 179 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P179 : ℚ := (1019198493541374571796748543597002034824082974525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P179 : RatPair2542 := ((985510712749976753156897225917488027741470920416088706048683692977194873243254319803317376092933 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-473762153714632160708743101616741241794191130087420758335576232486530214825812063809586350797173 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P179 : ℚ := (48313005605203001411019011731067113760122242023187 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P179 :
    phaseExp2646 phaseArg2658P179 20 =
      ((phaseValue2658P179.1,
        phaseValue2658P179.2), phaseRadius2658P179) := by
  decide +kernel

theorem phaseCosPin2658P179 :
    |Real.cos (phaseArg2658P179 : ℝ) -
      (phaseValue2658P179.1 : ℝ)| ≤
        (phaseRadius2658P179 : ℝ) := by
  have hsmall : |((phaseArg2658P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P179]
  have h := phaseExp_cos_error2646 phaseArg2658P179 20 hsmall
  rw [phaseChain2658P179] at h
  simpa [phaseValue2658P179] using h

theorem phaseSinPin2658P179 :
    |Real.sin (phaseArg2658P179 : ℝ) -
      (phaseValue2658P179.2 : ℝ)| ≤
        (phaseRadius2658P179 : ℝ) := by
  have hsmall : |((phaseArg2658P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P179]
  have h := phaseExp_sin_error2646 phaseArg2658P179 20 hsmall
  rw [phaseChain2658P179] at h
  simpa [phaseValue2658P179] using h

end ConnesWeilRH.Dev
