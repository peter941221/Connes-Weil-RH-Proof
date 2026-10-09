import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P155 : ℚ := ((-795632047113497051272102424729866400193 : ℚ) / 15440998431260016693751042404043980800)

def momentPanelGrowth2622K20P155 : ℚ := ((2541218983334914551279430473270630814849 : ℚ) / 2019033760525589366605774273880313036800)

theorem momentPanelPhase_owner2622K20P155 :
    (momentPanelPhase2622K20P155 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P155 :
    (momentPanelGrowth2622K20P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P155Input : RatPair2542 := (momentPanelPhase2622K20P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P155Expected : RatState2542 :=
  ((((1397726547350029086841253564988647263086875728548849739941006403499404427 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((28955118379895810161873989 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K20P155_replay :
    compactExp2620 momentScalarAmp2622K20P155Input 20 = momentScalarAmp2622K20P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K20P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P155_replay] at h
  simpa only [momentPanelPhase_owner2622K20P155] using h

theorem momentScalarAmp2622K20P155_radius_le :
    (momentScalarAmp2622K20P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P155Expected]

def momentScalarGrow2622K20P155Input : RatPair2542 := (momentPanelGrowth2622K20P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P155Expected : RatState2542 :=
  ((((3759977299332448233894453263993535067300916247047344534831993842229084744985468560504561758893669 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4766331759196049107558472030215495903398812681937 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K20P155_replay :
    compactExp2620 momentScalarGrow2622K20P155Input 20 = momentScalarGrow2622K20P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P155] using h

theorem momentScalarGrow2622K20P155_radius_le :
    (momentScalarGrow2622K20P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P155Expected]

end ConnesWeilRH.Dev
