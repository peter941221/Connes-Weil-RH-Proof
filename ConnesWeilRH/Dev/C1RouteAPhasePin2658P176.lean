import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 176 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P176 : ℚ := (983013931640497368064319601220777110510801922175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P176 : RatPair2542 := ((385787326557702864628483974141191838422136610023753739961543915062477539200689231000478621024403 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-497940331031994518900006562135684162441401063471963325474788557311844604838165878662899399148051 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P176 : ℚ := (14495785391325214438834516108203563444019934428959 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P176 :
    phaseExp2646 phaseArg2658P176 20 =
      ((phaseValue2658P176.1,
        phaseValue2658P176.2), phaseRadius2658P176) := by
  decide +kernel

theorem phaseCosPin2658P176 :
    |Real.cos (phaseArg2658P176 : ℝ) -
      (phaseValue2658P176.1 : ℝ)| ≤
        (phaseRadius2658P176 : ℝ) := by
  have hsmall : |((phaseArg2658P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P176]
  have h := phaseExp_cos_error2646 phaseArg2658P176 20 hsmall
  rw [phaseChain2658P176] at h
  simpa [phaseValue2658P176] using h

theorem phaseSinPin2658P176 :
    |Real.sin (phaseArg2658P176 : ℝ) -
      (phaseValue2658P176.2 : ℝ)| ≤
        (phaseRadius2658P176 : ℝ) := by
  have hsmall : |((phaseArg2658P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P176]
  have h := phaseExp_sin_error2646 phaseArg2658P176 20 hsmall
  rw [phaseChain2658P176] at h
  simpa [phaseValue2658P176] using h

end ConnesWeilRH.Dev
