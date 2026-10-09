import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P136 : ℚ := ((-2392162603442116095118251089032449844773 : ℚ) / 63587382348408351946117027506788761600)

def momentPanelGrowth2622K05P136 : ℚ := ((9822295652195309067946899929568550764203 : ℚ) / 20518929880883213830845548564800182681600)

theorem momentPanelPhase_owner2622K05P136 :
    (momentPanelPhase2622K05P136 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (93 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P136 :
    (momentPanelGrowth2622K05P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P136Input : RatPair2542 := (momentPanelPhase2622K05P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P136Expected : RatState2542 :=
  ((((49020095078675327570168508158902477065240395420326905551028702997461049981000491 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((31071291813582280833536813196861 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P136_replay :
    compactExp2620 momentScalarAmp2622K05P136Input 20 = momentScalarAmp2622K05P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K05P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P136_replay] at h
  simpa only [momentPanelPhase_owner2622K05P136] using h

theorem momentScalarAmp2622K05P136_radius_le :
    (momentScalarAmp2622K05P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P136Expected]

def momentScalarGrow2622K05P136Input : RatPair2542 := (momentPanelGrowth2622K05P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P136Expected : RatState2542 :=
  ((((1723704948256718008301978598709712385565007765419355417762818270856973158143659816188247573446191 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2185054614755914800233996227807683901516833358551 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P136_replay :
    compactExp2620 momentScalarGrow2622K05P136Input 20 = momentScalarGrow2622K05P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P136] using h

theorem momentScalarGrow2622K05P136_radius_le :
    (momentScalarGrow2622K05P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P136Expected]

end ConnesWeilRH.Dev
