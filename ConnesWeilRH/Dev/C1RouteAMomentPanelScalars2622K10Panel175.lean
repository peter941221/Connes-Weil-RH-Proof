import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P175 : ℚ := ((-2404992142236872974027326032266148132859 : ℚ) / 21821844492568832209124847658624614400)

def momentPanelGrowth2622K10P175 : ℚ := ((1092398354302229070340587999772684582523 : ℚ) / 143261757873953026288987817371081113600)

theorem momentPanelPhase_owner2622K10P175 :
    (momentPanelPhase2622K10P175 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (171 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P175, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P175 :
    (momentPanelGrowth2622K10P175 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P175, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P175Input : RatPair2542 := (momentPanelPhase2622K10P175 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P175Expected : RatState2542 :=
  ((((730821323217479796677900885488929784646158699567 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208925819614629174706181 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K10P175_replay :
    compactExp2620 momentScalarAmp2622K10P175Input 20 = momentScalarAmp2622K10P175Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P175_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (171 / 200) 0) -
      (momentScalarAmp2622K10P175Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P175]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P175 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P175 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P175Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P175_replay] at h
  simpa only [momentPanelPhase_owner2622K10P175] using h

theorem momentScalarAmp2622K10P175_radius_le :
    (momentScalarAmp2622K10P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P175Expected]

def momentScalarGrow2622K10P175Input : RatPair2542 := (momentPanelGrowth2622K10P175 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P175Expected : RatState2542 :=
  ((((2188503557313492244480050831127006562786383308681840583038285432423725849536429652764128633875558155 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1387118836920365804412461602168084024257401541932473 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K10P175_replay :
    compactExp2620 momentScalarGrow2622K10P175Input 20 = momentScalarGrow2622K10P175Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P175_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P175Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P175]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P175 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P175 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P175Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P175_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P175] using h

theorem momentScalarGrow2622K10P175_radius_le :
    (momentScalarGrow2622K10P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P175Expected]

end ConnesWeilRH.Dev
