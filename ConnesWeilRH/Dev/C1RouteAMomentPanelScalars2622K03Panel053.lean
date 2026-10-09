import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P053 : ℚ := ((-73303213734361464639470180004269540652827047784323925 : ℚ) / 2111321802829155628209998201462760357270451549896704)

def momentPanelGrowth2622K03P053 : ℚ := ((682659088947971745122469669097369613661265176653395475 : ℚ) / 2268194547356081088834065181700517803912816738783199232)

theorem momentPanelPhase_owner2622K03P053 :
    (momentPanelPhase2622K03P053 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P053 :
    (momentPanelGrowth2622K03P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P053Input : RatPair2542 := (momentPanelPhase2622K03P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P053Expected : RatState2542 :=
  ((((445882850921311006911515294535602175687299887049606591148044421767843465275170865 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((141310594870141298226476831135915 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K03P053_replay :
    compactExp2620 momentScalarAmp2622K03P053Input 20 = momentScalarAmp2622K03P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K03P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P053_replay] at h
  simpa only [momentPanelPhase_owner2622K03P053] using h

theorem momentScalarAmp2622K03P053_radius_le :
    (momentScalarAmp2622K03P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P053Expected]

def momentScalarGrow2622K03P053Input : RatPair2542 := (momentPanelGrowth2622K03P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P053Expected : RatState2542 :=
  ((((360759973202278320459843105221319757640057442981520406306590124544206409877288696206393067348613 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((914634930610868364860993065159500017573723506541 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P053_replay :
    compactExp2620 momentScalarGrow2622K03P053Input 20 = momentScalarGrow2622K03P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P053] using h

theorem momentScalarGrow2622K03P053_radius_le :
    (momentScalarGrow2622K03P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P053Expected]

end ConnesWeilRH.Dev
