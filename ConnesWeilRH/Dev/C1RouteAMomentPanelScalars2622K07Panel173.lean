import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P173 : ℚ := ((-30243891335327034888813827377901462575 : ℚ) / 327520350279767174005900213766586368)

def momentPanelGrowth2622K07P173 : ℚ := ((126516852777788857167679620935913675 : ℚ) / 21458789360663467308536191860604928)

theorem momentPanelPhase_owner2622K07P173 :
    (momentPanelPhase2622K07P173 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P173 :
    (momentPanelGrowth2622K07P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P173Input : RatPair2542 := (momentPanelPhase2622K07P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P173Expected : RatState2542 :=
  ((((84127520330834519271423182343959629640751186602630709643 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614629281381329 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P173_replay :
    compactExp2620 momentScalarAmp2622K07P173Input 20 = momentScalarAmp2622K07P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K07P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P173_replay] at h
  simpa only [momentPanelPhase_owner2622K07P173] using h

theorem momentScalarAmp2622K07P173_radius_le :
    (momentScalarAmp2622K07P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P173Expected]

def momentScalarGrow2622K07P173Input : RatPair2542 := (momentPanelGrowth2622K07P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P173Expected : RatState2542 :=
  ((((97056474174306065218364388857515816850590882775995877526914859769462987805319936280488948407870019 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((492132023864461090238708239213252331903089966728129 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P173_replay :
    compactExp2620 momentScalarGrow2622K07P173Input 20 = momentScalarGrow2622K07P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P173] using h

theorem momentScalarGrow2622K07P173_radius_le :
    (momentScalarGrow2622K07P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P173Expected]

end ConnesWeilRH.Dev
