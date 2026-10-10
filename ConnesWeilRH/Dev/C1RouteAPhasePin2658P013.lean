import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 013 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P013 : ℚ := (-983013931640497368064319601220777110510801922175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P013 : RatPair2542 := ((771574653115405729256967948282383676844273220047507479923087830124955078401378462000957244013489 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (497940331031994518900006562135684162441401063471963325474788557311844604838165878662899398964303 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P013 : ℚ := (14495785391325214438834516108203563444019934428959 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P013 :
    phaseExp2646 phaseArg2658P013 20 =
      ((phaseValue2658P013.1,
        phaseValue2658P013.2), phaseRadius2658P013) := by
  decide +kernel

theorem phaseCosPin2658P013 :
    |Real.cos (phaseArg2658P013 : ℝ) -
      (phaseValue2658P013.1 : ℝ)| ≤
        (phaseRadius2658P013 : ℝ) := by
  have hsmall : |((phaseArg2658P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P013]
  have h := phaseExp_cos_error2646 phaseArg2658P013 20 hsmall
  rw [phaseChain2658P013] at h
  simpa [phaseValue2658P013] using h

theorem phaseSinPin2658P013 :
    |Real.sin (phaseArg2658P013 : ℝ) -
      (phaseValue2658P013.2 : ℝ)| ≤
        (phaseRadius2658P013 : ℝ) := by
  have hsmall : |((phaseArg2658P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P013]
  have h := phaseExp_sin_error2646 phaseArg2658P013 20 hsmall
  rw [phaseChain2658P013] at h
  simpa [phaseValue2658P013] using h

end ConnesWeilRH.Dev
