import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 149 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P149 : ℚ := (657352874532602534472459119834752791691272451025 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P149 : RatPair2542 := ((-1241373242816780920668261516504834601328234738020765605792750943483020512177707536144374837042463 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1738226996005051319254336850436162223285337418691537341126848286548460757075018354109843329782565 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P149 : ℚ := (25986666280883858991290265745536055741584302368081 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P149 :
    phaseExp2646 phaseArg2658P149 20 =
      ((phaseValue2658P149.1,
        phaseValue2658P149.2), phaseRadius2658P149) := by
  decide +kernel

theorem phaseCosPin2658P149 :
    |Real.cos (phaseArg2658P149 : ℝ) -
      (phaseValue2658P149.1 : ℝ)| ≤
        (phaseRadius2658P149 : ℝ) := by
  have hsmall : |((phaseArg2658P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P149]
  have h := phaseExp_cos_error2646 phaseArg2658P149 20 hsmall
  rw [phaseChain2658P149] at h
  simpa [phaseValue2658P149] using h

theorem phaseSinPin2658P149 :
    |Real.sin (phaseArg2658P149 : ℝ) -
      (phaseValue2658P149.2 : ℝ)| ≤
        (phaseRadius2658P149 : ℝ) := by
  have hsmall : |((phaseArg2658P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P149]
  have h := phaseExp_sin_error2646 phaseArg2658P149 20 hsmall
  rw [phaseChain2658P149] at h
  simpa [phaseValue2658P149] using h

end ConnesWeilRH.Dev
