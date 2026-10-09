import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P010 : ℚ := ((-62340321 : ℚ) / 735950)

def momentPanelGrowth2622K06P010 : ℚ := ((2527 : ℚ) / 675)

theorem momentPanelPhase_owner2622K06P010 :
    (momentPanelPhase2622K06P010 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P010 :
    (momentPanelGrowth2622K06P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P010Input : RatPair2542 := (momentPanelPhase2622K06P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P010Expected : RatState2542 :=
  ((((174046521712453370373416259082857315116603862251730428896597 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((604462909807424911841939 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P010_replay :
    compactExp2620 momentScalarAmp2622K06P010Input 20 = momentScalarAmp2622K06P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K06P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P010_replay] at h
  simpa only [momentPanelPhase_owner2622K06P010] using h

theorem momentScalarAmp2622K06P010_radius_le :
    (momentScalarAmp2622K06P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P010Expected]

def momentScalarGrow2622K06P010Input : RatPair2542 := (momentPanelGrowth2622K06P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P010Expected : RatState2542 :=
  ((((90254418589757931214042116754966329874743053637058389550179397772793793224458376611458572062737547 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57205329710208303897893570035696208778475826429599 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P010_replay :
    compactExp2620 momentScalarGrow2622K06P010Input 20 = momentScalarGrow2622K06P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P010] using h

theorem momentScalarGrow2622K06P010_radius_le :
    (momentScalarGrow2622K06P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P010Expected]

end ConnesWeilRH.Dev
