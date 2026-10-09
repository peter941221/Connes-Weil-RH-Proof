import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P168 : ℚ := ((-29820788757076577301102352723731633325 : ℚ) / 415140359767542390237352339322175488)

def momentPanelGrowth2622K07P168 : ℚ := ((656349676158489526634258597956439514025 : ℚ) / 191061393716517332583786000265840164864)

theorem momentPanelPhase_owner2622K07P168 :
    (momentPanelPhase2622K07P168 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P168 :
    (momentPanelGrowth2622K07P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P168Input : RatPair2542 := (momentPanelPhase2622K07P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P168Expected : RatState2542 :=
  ((((33950899701522839589297013210423916477272021821007930750793511559 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((151115738212035425357629 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K07P168_replay :
    compactExp2620 momentScalarAmp2622K07P168Input 20 = momentScalarAmp2622K07P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K07P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P168_replay] at h
  simpa only [momentPanelPhase_owner2622K07P168] using h

theorem momentScalarAmp2622K07P168_radius_le :
    (momentScalarAmp2622K07P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P168Expected]

def momentScalarGrow2622K07P168Input : RatPair2542 := (momentPanelGrowth2622K07P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P168Expected : RatState2542 :=
  ((((33150678936260953214888643317546401749367370421858553208286724232623625426259761875444629562522753 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((21011670188481351445370182721007238594839840818427 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P168_replay :
    compactExp2620 momentScalarGrow2622K07P168Input 20 = momentScalarGrow2622K07P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P168] using h

theorem momentScalarGrow2622K07P168_radius_le :
    (momentScalarGrow2622K07P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P168Expected]

end ConnesWeilRH.Dev
