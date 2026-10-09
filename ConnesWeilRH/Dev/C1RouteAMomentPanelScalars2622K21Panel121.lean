import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K21
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K21P121 : ℚ := ((-2398235686199662276088523934351659542343 : ℚ) / 73079550042917333704524341108644249600)

def momentPanelGrowth2622K21P121 : ℚ := ((27000754571342985777458058876759765683 : ℚ) / 106388337214514289458251714533104025600)

theorem momentPanelPhase_owner2622K21P121 :
    (momentPanelPhase2622K21P121 : ℝ) = momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (63 / 200) 0 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P121, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K21P121 :
    (momentPanelGrowth2622K21P121 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2))
      (63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P121, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K21P121Input : RatPair2542 := (momentPanelPhase2622K21P121 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K21P121Expected : RatState2542 :=
  ((((2988072587864760746666475529714987796560312268847083992445270671620801313398160263 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((946987639490332466331224609375347 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K21P121_replay :
    compactExp2620 momentScalarAmp2622K21P121Input 20 = momentScalarAmp2622K21P121Expected := by
  decide +kernel

theorem momentScalarAmp2622K21P121_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (63 / 200) 0) -
      (momentScalarAmp2622K21P121Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K21P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K21P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P121]
  have h := compactExp_real_error2620 momentPanelPhase2622K21P121 20 hsmall
  change |Real.exp (momentPanelPhase2622K21P121 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K21P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K21P121Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K21P121_replay] at h
  simpa only [momentPanelPhase_owner2622K21P121] using h

theorem momentScalarAmp2622K21P121_radius_le :
    (momentScalarAmp2622K21P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarAmp2622K21P121Expected]

def momentScalarGrow2622K21P121Input : RatPair2542 := (momentPanelGrowth2622K21P121 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K21P121Expected : RatState2542 :=
  ((((2753087918435403688533707780969681347621365648222613223106947911878238130297483635743729128498519 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((872488176896885207656522184144190791578673643843 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K21P121_replay :
    compactExp2620 momentScalarGrow2622K21P121Input 20 = momentScalarGrow2622K21P121Expected := by
  decide +kernel

theorem momentScalarGrow2622K21P121_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K21P121Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K21P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K21P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P121]
  have h := compactExp_real_error2620 momentPanelGrowth2622K21P121 20 hsmall
  change |Real.exp (momentPanelGrowth2622K21P121 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K21P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K21P121Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K21P121_replay] at h
  simpa only [momentPanelGrowth_owner2622K21P121] using h

theorem momentScalarGrow2622K21P121_radius_le :
    (momentScalarGrow2622K21P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarGrow2622K21P121Expected]

end ConnesWeilRH.Dev
