import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 146 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P146 : ℚ := (621168312631725330740030177458527867377991398675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P146 : RatPair2542 := ((-356161443750624358927575802292120100488145976575337515062269558476668527716625391580350828852239 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (-1591485165934552049469384357574612976073229540980234996135516853838486128132663762186520940962881 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P146 : ℚ := (23238437383040818756088687539312000912234384181693 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P146 :
    phaseExp2646 phaseArg2658P146 20 =
      ((phaseValue2658P146.1,
        phaseValue2658P146.2), phaseRadius2658P146) := by
  decide +kernel

theorem phaseCosPin2658P146 :
    |Real.cos (phaseArg2658P146 : ℝ) -
      (phaseValue2658P146.1 : ℝ)| ≤
        (phaseRadius2658P146 : ℝ) := by
  have hsmall : |((phaseArg2658P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P146]
  have h := phaseExp_cos_error2646 phaseArg2658P146 20 hsmall
  rw [phaseChain2658P146] at h
  simpa [phaseValue2658P146] using h

theorem phaseSinPin2658P146 :
    |Real.sin (phaseArg2658P146 : ℝ) -
      (phaseValue2658P146.2 : ℝ)| ≤
        (phaseRadius2658P146 : ℝ) := by
  have hsmall : |((phaseArg2658P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P146]
  have h := phaseExp_sin_error2646 phaseArg2658P146 20 hsmall
  rw [phaseChain2658P146] at h
  simpa [phaseValue2658P146] using h

end ConnesWeilRH.Dev
