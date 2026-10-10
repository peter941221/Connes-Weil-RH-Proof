import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 127 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P127 : ℚ := (391999420592836373767980209075770013393878067125 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P127 : RatPair2542 := ((661337314551526575992967854497096326449689578031732669417090591646669622576584710720076782484949 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-1677191832543104175514203569613377613651510900038290591052967278443185055020388873276992986015389 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P127 : ℚ := (18078158389786037600550903916221471987778815989229 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P127 :
    phaseExp2646 phaseArg2658P127 20 =
      ((phaseValue2658P127.1,
        phaseValue2658P127.2), phaseRadius2658P127) := by
  decide +kernel

theorem phaseCosPin2658P127 :
    |Real.cos (phaseArg2658P127 : ℝ) -
      (phaseValue2658P127.1 : ℝ)| ≤
        (phaseRadius2658P127 : ℝ) := by
  have hsmall : |((phaseArg2658P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P127]
  have h := phaseExp_cos_error2646 phaseArg2658P127 20 hsmall
  rw [phaseChain2658P127] at h
  simpa [phaseValue2658P127] using h

theorem phaseSinPin2658P127 :
    |Real.sin (phaseArg2658P127 : ℝ) -
      (phaseValue2658P127.2 : ℝ)| ≤
        (phaseRadius2658P127 : ℝ) := by
  have hsmall : |((phaseArg2658P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P127]
  have h := phaseExp_sin_error2646 phaseArg2658P127 20 hsmall
  rw [phaseChain2658P127] at h
  simpa [phaseValue2658P127] using h

end ConnesWeilRH.Dev
