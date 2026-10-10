import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 006 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P006 : ℚ := (-1067444576075877510106653800098635267241791044325 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P006 : RatPair2542 := ((-2124757549824242755332575837868025597001538330981994935117374097334094345077860867512301127358385 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (54684305385020997676478969436031714488965490321092433173303551183337928604658110209891580234021 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P006 : ℚ := (38082977885313918245754348572741303299181413926991 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P006 :
    phaseExp2646 phaseArg2658P006 20 =
      ((phaseValue2658P006.1,
        phaseValue2658P006.2), phaseRadius2658P006) := by
  decide +kernel

theorem phaseCosPin2658P006 :
    |Real.cos (phaseArg2658P006 : ℝ) -
      (phaseValue2658P006.1 : ℝ)| ≤
        (phaseRadius2658P006 : ℝ) := by
  have hsmall : |((phaseArg2658P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P006]
  have h := phaseExp_cos_error2646 phaseArg2658P006 20 hsmall
  rw [phaseChain2658P006] at h
  simpa [phaseValue2658P006] using h

theorem phaseSinPin2658P006 :
    |Real.sin (phaseArg2658P006 : ℝ) -
      (phaseValue2658P006.2 : ℝ)| ≤
        (phaseRadius2658P006 : ℝ) := by
  have hsmall : |((phaseArg2658P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P006]
  have h := phaseExp_sin_error2646 phaseArg2658P006 20 hsmall
  rw [phaseChain2658P006] at h
  simpa [phaseValue2658P006] using h

end ConnesWeilRH.Dev
