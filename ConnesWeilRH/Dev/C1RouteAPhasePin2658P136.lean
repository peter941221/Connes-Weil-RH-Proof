import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 136 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P136 : ℚ := (500553106295467984965267036204444786333721224175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P136 : RatPair2542 := ((1794691732615586757591061795966926096185834191551916227238418492247035104969869446452989165826035 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-579120497501050826410156214507933881986617931474085586814318896382996253737093693874698291083517 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P136 : ℚ := (11256610229219987579141983176723203452373217580715 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P136 :
    phaseExp2646 phaseArg2658P136 20 =
      ((phaseValue2658P136.1,
        phaseValue2658P136.2), phaseRadius2658P136) := by
  decide +kernel

theorem phaseCosPin2658P136 :
    |Real.cos (phaseArg2658P136 : ℝ) -
      (phaseValue2658P136.1 : ℝ)| ≤
        (phaseRadius2658P136 : ℝ) := by
  have hsmall : |((phaseArg2658P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P136]
  have h := phaseExp_cos_error2646 phaseArg2658P136 20 hsmall
  rw [phaseChain2658P136] at h
  simpa [phaseValue2658P136] using h

theorem phaseSinPin2658P136 :
    |Real.sin (phaseArg2658P136 : ℝ) -
      (phaseValue2658P136.2 : ℝ)| ≤
        (phaseRadius2658P136 : ℝ) := by
  have hsmall : |((phaseArg2658P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P136]
  have h := phaseExp_sin_error2646 phaseArg2658P136 20 hsmall
  rw [phaseChain2658P136] at h
  simpa [phaseValue2658P136] using h

end ConnesWeilRH.Dev
