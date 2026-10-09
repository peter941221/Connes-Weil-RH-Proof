import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P172 : ℚ := ((-2641916120657262438538980531864637011990995866279023 : ℚ) / 29172942838909819968831365215547680587663340994560)

def momentPanelGrowth2622K02P172 : ℚ := ((2388056239707824706896126611050376603652158585759865653 : ℚ) / 460445377217254611400130377404280240595033356291276800)

theorem momentPanelPhase_owner2622K02P172 :
    (momentPanelPhase2622K02P172 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P172 :
    (momentPanelGrowth2622K02P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P172Input : RatPair2542 := (momentPanelPhase2622K02P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P172Expected : RatState2542 :=
  ((((999253560768872470509887697069005479972315040326314245841 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807314904082681 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P172_replay :
    compactExp2620 momentScalarAmp2622K02P172Input 20 = momentScalarAmp2622K02P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K02P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P172_replay] at h
  simpa only [momentPanelPhase_owner2622K02P172] using h

theorem momentScalarAmp2622K02P172_radius_le :
    (momentScalarAmp2622K02P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P172Expected]

def momentScalarGrow2622K02P172Input : RatPair2542 := (momentPanelGrowth2622K02P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P172Expected : RatState2542 :=
  ((((381966887762894380295213981275875547759771082857649474418475608012238697330431782935218071914507261 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((30262384976343671800569508152595133853603364623767 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K02P172_replay :
    compactExp2620 momentScalarGrow2622K02P172Input 20 = momentScalarGrow2622K02P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P172] using h

theorem momentScalarGrow2622K02P172_radius_le :
    (momentScalarGrow2622K02P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P172Expected]

end ConnesWeilRH.Dev
