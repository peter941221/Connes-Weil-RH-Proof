import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 117 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P117 : ℚ := (271384214256579027993217067821686932349607892625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P117 : RatPair2542 := ((1449716670180328618936079532008046294431017352313308251276931242817750925847455795269337799505395 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1568681673834259947082724415685418932886503355318735946213517305578162810222438198915805805321671 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P117 : ℚ := (1505635665543431328370311162010610176952624299645 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P117 :
    phaseExp2646 phaseArg2658P117 20 =
      ((phaseValue2658P117.1,
        phaseValue2658P117.2), phaseRadius2658P117) := by
  decide +kernel

theorem phaseCosPin2658P117 :
    |Real.cos (phaseArg2658P117 : ℝ) -
      (phaseValue2658P117.1 : ℝ)| ≤
        (phaseRadius2658P117 : ℝ) := by
  have hsmall : |((phaseArg2658P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P117]
  have h := phaseExp_cos_error2646 phaseArg2658P117 20 hsmall
  rw [phaseChain2658P117] at h
  simpa [phaseValue2658P117] using h

theorem phaseSinPin2658P117 :
    |Real.sin (phaseArg2658P117 : ℝ) -
      (phaseValue2658P117.2 : ℝ)| ≤
        (phaseRadius2658P117 : ℝ) := by
  have hsmall : |((phaseArg2658P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P117]
  have h := phaseExp_sin_error2646 phaseArg2658P117 20 hsmall
  rw [phaseChain2658P117] at h
  simpa [phaseValue2658P117] using h

end ConnesWeilRH.Dev
