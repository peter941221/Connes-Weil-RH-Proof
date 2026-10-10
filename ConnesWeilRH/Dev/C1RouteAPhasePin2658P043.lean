import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 043 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P043 : ℚ := (-621168312631725330740030177458527867377991398675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P043 : RatPair2542 := ((-1424645775002497435710303209168480401952583906301350060249078233906674110866501566321403313867087 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (397871291483638012367346089393653244018307385245058749033879213459621532033165940546630235595863 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P043 : ℚ := (23238437383040818756088687539312000912234384181693 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P043 :
    phaseExp2646 phaseArg2658P043 20 =
      ((phaseValue2658P043.1,
        phaseValue2658P043.2), phaseRadius2658P043) := by
  decide +kernel

theorem phaseCosPin2658P043 :
    |Real.cos (phaseArg2658P043 : ℝ) -
      (phaseValue2658P043.1 : ℝ)| ≤
        (phaseRadius2658P043 : ℝ) := by
  have hsmall : |((phaseArg2658P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P043]
  have h := phaseExp_cos_error2646 phaseArg2658P043 20 hsmall
  rw [phaseChain2658P043] at h
  simpa [phaseValue2658P043] using h

theorem phaseSinPin2658P043 :
    |Real.sin (phaseArg2658P043 : ℝ) -
      (phaseValue2658P043.2 : ℝ)| ≤
        (phaseRadius2658P043 : ℝ) := by
  have hsmall : |((phaseArg2658P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P043]
  have h := phaseExp_sin_error2646 phaseArg2658P043 20 hsmall
  rw [phaseChain2658P043] at h
  simpa [phaseValue2658P043] using h

end ConnesWeilRH.Dev
