import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P058 : ℚ := ((-373220056411396860720657200513403941448410373607899231 : ℚ) / 10285032323177688094882220353046951851801348721868800)

def momentPanelGrowth2622K04P058 : ℚ := ((4986038796734490918630539035387506773673638688731989 : ℚ) / 14972827369870413324218160619703818627250480008396800)

theorem momentPanelPhase_owner2622K04P058 :
    (momentPanelPhase2622K04P058 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-63 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P058 :
    (momentPanelGrowth2622K04P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P058Input : RatPair2542 := (momentPanelPhase2622K04P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P058Expected : RatState2542 :=
  ((((185791325807173686311575367607965538587736330545663733815871523138862643611804195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((7360207422793983448001204418787 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K04P058_replay :
    compactExp2620 momentScalarAmp2622K04P058Input 20 = momentScalarAmp2622K04P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K04P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P058_replay] at h
  simpa only [momentPanelPhase_owner2622K04P058] using h

theorem momentScalarAmp2622K04P058_radius_le :
    (momentScalarAmp2622K04P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P058Expected]

def momentScalarGrow2622K04P058Input : RatPair2542 := (momentPanelGrowth2622K04P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P058Expected : RatState2542 :=
  ((((1490016957242117311875672927019155533942693758196882142834506486510329799775226878819773580593297 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3777640580696508548888137135928785118854901327137 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P058_replay :
    compactExp2620 momentScalarGrow2622K04P058Input 20 = momentScalarGrow2622K04P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P058] using h

theorem momentScalarGrow2622K04P058_radius_le :
    (momentScalarGrow2622K04P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P058Expected]

end ConnesWeilRH.Dev
