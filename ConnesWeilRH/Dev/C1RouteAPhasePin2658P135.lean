import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 135 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P135 : ℚ := (488491585661842250387790722079036478229294206725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P135 : RatPair2542 := ((45958861541898080471895220872198189130623246400628613121904524815357534557261019463229131259097 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), (1064030679345590754302700250707727827911898351477594320561583062367647876777607977385694357445713 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P135 : ℚ := (11752294485438849308358682434257792827508524195193 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P135 :
    phaseExp2646 phaseArg2658P135 20 =
      ((phaseValue2658P135.1,
        phaseValue2658P135.2), phaseRadius2658P135) := by
  decide +kernel

theorem phaseCosPin2658P135 :
    |Real.cos (phaseArg2658P135 : ℝ) -
      (phaseValue2658P135.1 : ℝ)| ≤
        (phaseRadius2658P135 : ℝ) := by
  have hsmall : |((phaseArg2658P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P135]
  have h := phaseExp_cos_error2646 phaseArg2658P135 20 hsmall
  rw [phaseChain2658P135] at h
  simpa [phaseValue2658P135] using h

theorem phaseSinPin2658P135 :
    |Real.sin (phaseArg2658P135 : ℝ) -
      (phaseValue2658P135.2 : ℝ)| ≤
        (phaseRadius2658P135 : ℝ) := by
  have hsmall : |((phaseArg2658P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P135]
  have h := phaseExp_sin_error2646 phaseArg2658P135 20 hsmall
  rw [phaseChain2658P135] at h
  simpa [phaseValue2658P135] using h

end ConnesWeilRH.Dev
