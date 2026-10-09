import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P095 : ℚ := ((-808999703644841563601715524601224648713 : ℚ) / 26961407086134165494553081134501068800)

def momentPanelGrowth2622K10P095 : ℚ := ((325638441355425111781964718814354239889 : ℚ) / 6292699723291825538294851697854172364800)

theorem momentPanelPhase_owner2622K10P095 :
    (momentPanelPhase2622K10P095 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (11 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P095, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P095 :
    (momentPanelGrowth2622K10P095 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P095, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P095Input : RatPair2542 := (momentPanelPhase2622K10P095 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P095Expected : RatState2542 :=
  ((((198713461470561442171770355625468407548192506463041523548564024322075961906650956121 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((125953223555218026730009894580698637 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K10P095_replay :
    compactExp2620 momentScalarAmp2622K10P095Input 20 = momentScalarAmp2622K10P095Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P095_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (11 / 200) 0) -
      (momentScalarAmp2622K10P095Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P095]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P095 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P095 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P095Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P095_replay] at h
  simpa only [momentPanelPhase_owner2622K10P095] using h

theorem momentScalarAmp2622K10P095_radius_le :
    (momentScalarAmp2622K10P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P095Expected]

def momentScalarGrow2622K10P095Input : RatPair2542 := (momentPanelGrowth2622K10P095 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P095Expected : RatState2542 :=
  ((((2249431366291275183814089438231541443682369221271109113892824176594151883415339147198459830071147 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((712873220231602255857292206922053503409656826271 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K10P095_replay :
    compactExp2620 momentScalarGrow2622K10P095Input 20 = momentScalarGrow2622K10P095Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P095_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P095Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P095]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P095 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P095 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P095Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P095_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P095] using h

theorem momentScalarGrow2622K10P095_radius_le :
    (momentScalarGrow2622K10P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P095Expected]

end ConnesWeilRH.Dev
