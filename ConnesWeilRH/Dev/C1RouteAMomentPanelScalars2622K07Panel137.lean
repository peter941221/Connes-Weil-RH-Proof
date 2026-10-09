import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P137 : ℚ := ((-1169577971444166668307175455814171375 : ℚ) / 33506540665232559540360859124498432)

def momentPanelGrowth2622K07P137 : ℚ := ((5321258977963851388777824917040618075 : ℚ) / 9385117136620908241909720009567895552)

theorem momentPanelPhase_owner2622K07P137 :
    (momentPanelPhase2622K07P137 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (19 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P137, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P137 :
    (momentPanelGrowth2622K07P137 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P137, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P137Input : RatPair2542 := (momentPanelPhase2622K07P137 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P137Expected : RatState2542 :=
  ((((739780298527459081217775263638710357008783967060634712653529225109663594595336361 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((937814158972917249633623005132803 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P137_replay :
    compactExp2620 momentScalarAmp2622K07P137Input 20 = momentScalarAmp2622K07P137Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P137_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (19 / 40) 0) -
      (momentScalarAmp2622K07P137Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P137]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P137 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P137 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P137Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P137_replay] at h
  simpa only [momentPanelPhase_owner2622K07P137] using h

theorem momentScalarAmp2622K07P137_radius_le :
    (momentScalarAmp2622K07P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P137Expected]

def momentScalarGrow2622K07P137Input : RatPair2542 := (momentPanelGrowth2622K07P137 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P137Expected : RatState2542 :=
  ((((3765640388743071571992014401326896768466061926032843558028240866714722768566329268296013679569051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((596689214735600673569342560402847605055897006625 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P137_replay :
    compactExp2620 momentScalarGrow2622K07P137Input 20 = momentScalarGrow2622K07P137Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P137_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P137Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P137]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P137 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P137 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P137Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P137_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P137] using h

theorem momentScalarGrow2622K07P137_radius_le :
    (momentScalarGrow2622K07P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P137Expected]

end ConnesWeilRH.Dev
