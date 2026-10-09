import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P116 : ℚ := ((-800976439587375354668139004826247586871 : ℚ) / 25144103185646975824567407419274035200)

def momentPanelGrowth2622K09P116 : ℚ := ((17778765105157649187323241613323282046729 : ℚ) / 87165116619304996749767357801108917452800)

theorem momentPanelPhase_owner2622K09P116 :
    (momentPanelPhase2622K09P116 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P116 :
    (momentPanelGrowth2622K09P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P116Input : RatPair2542 := (momentPanelPhase2622K09P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P116Expected : RatState2542 :=
  ((((31257722682043743880972908695127470667236127270435092679106178348864293868145610985 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19812537351110699594289533428291561 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K09P116_replay :
    compactExp2620 momentScalarAmp2622K09P116Input 20 = momentScalarAmp2622K09P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K09P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P116_replay] at h
  simpa only [momentPanelPhase_owner2622K09P116] using h

theorem momentScalarAmp2622K09P116_radius_le :
    (momentScalarAmp2622K09P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P116Expected]

def momentScalarGrow2622K09P116Input : RatPair2542 := (momentPanelGrowth2622K09P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P116Expected : RatState2542 :=
  ((((1309634625710667606088938954087466252190781643610153484037097699872270602112260537016568022025275 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((830079398215809566463348591501389503583055414339 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K09P116_replay :
    compactExp2620 momentScalarGrow2622K09P116Input 20 = momentScalarGrow2622K09P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P116] using h

theorem momentScalarGrow2622K09P116_radius_le :
    (momentScalarGrow2622K09P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P116Expected]

end ConnesWeilRH.Dev
