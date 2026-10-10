import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 003 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P003 : ℚ := (-1103629137976754713839082742474860191555072096675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P003 : RatPair2542 := ((-2087915676866717406995192128523063557631045684631691046424022961968897140988558736463332304816035 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (450609302962547057571403952644359651245827170528227278193834438925749046285346280443073055529317 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P003 : ℚ := (2333379102527036670007225021082522755332082550363 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P003 :
    phaseExp2646 phaseArg2658P003 20 =
      ((phaseValue2658P003.1,
        phaseValue2658P003.2), phaseRadius2658P003) := by
  decide +kernel

theorem phaseCosPin2658P003 :
    |Real.cos (phaseArg2658P003 : ℝ) -
      (phaseValue2658P003.1 : ℝ)| ≤
        (phaseRadius2658P003 : ℝ) := by
  have hsmall : |((phaseArg2658P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P003]
  have h := phaseExp_cos_error2646 phaseArg2658P003 20 hsmall
  rw [phaseChain2658P003] at h
  simpa [phaseValue2658P003] using h

theorem phaseSinPin2658P003 :
    |Real.sin (phaseArg2658P003 : ℝ) -
      (phaseValue2658P003.2 : ℝ)| ≤
        (phaseRadius2658P003 : ℝ) := by
  have hsmall : |((phaseArg2658P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P003]
  have h := phaseExp_sin_error2646 phaseArg2658P003 20 hsmall
  rw [phaseChain2658P003] at h
  simpa [phaseValue2658P003] using h

end ConnesWeilRH.Dev
