import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P152 : ℚ := ((-46601026564626907912898845844829085 : ℚ) / 1054685299389886862045257066872832)

def momentPanelGrowth2622K07P152 : ℚ := ((1652473113460041375543434465576456838075 : ℚ) / 1475462586999295331830173674166919626752)

theorem momentPanelPhase_owner2622K07P152 :
    (momentPanelPhase2622K07P152 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (5 / 8) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P152 :
    (momentPanelGrowth2622K07P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P152Input : RatPair2542 := (momentPanelPhase2622K07P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P152Expected : RatState2542 :=
  ((((138164716865875615600656467719129687722078739738035277642670353771951281519229 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((43788596123503468987815581013 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P152_replay :
    compactExp2620 momentScalarAmp2622K07P152Input 20 = momentScalarAmp2622K07P152Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622K07P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P152]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P152 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P152_replay] at h
  simpa only [momentPanelPhase_owner2622K07P152] using h

theorem momentScalarAmp2622K07P152_radius_le :
    (momentScalarAmp2622K07P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P152Expected]

def momentScalarGrow2622K07P152Input : RatPair2542 := (momentPanelGrowth2622K07P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P152Expected : RatState2542 :=
  ((((6546289258575775378613954880425322695576069131225790530637634549132978155005794500723969206360899 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4149199322245863806229682883529373283957053908659 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P152_replay :
    compactExp2620 momentScalarGrow2622K07P152Input 20 = momentScalarGrow2622K07P152Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P152_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P152] using h

theorem momentScalarGrow2622K07P152_radius_le :
    (momentScalarGrow2622K07P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P152Expected]

end ConnesWeilRH.Dev
