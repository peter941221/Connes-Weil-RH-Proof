import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P020 : ℚ := ((-35589760807373566533422282729316721525 : ℚ) / 559226597591883856929073612458033152)

def momentPanelGrowth2622K07P020 : ℚ := ((59630207648357247266360675186611825 : ℚ) / 35169698252731996515124533729951744)

theorem momentPanelPhase_owner2622K07P020 :
    (momentPanelPhase2622K07P020 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-139 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P020 :
    (momentPanelGrowth2622K07P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P020Input : RatPair2542 := (momentPanelPhase2622K07P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P020Expected : RatState2542 :=
  ((((245254652827494006696724233925154506308736610146905070953915770918563 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((604618367846166566725355 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P020_replay :
    compactExp2620 momentScalarAmp2622K07P020Input 20 = momentScalarAmp2622K07P020Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622K07P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P020]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P020 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P020_replay] at h
  simpa only [momentPanelPhase_owner2622K07P020] using h

theorem momentScalarAmp2622K07P020_radius_le :
    (momentScalarAmp2622K07P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P020Expected]

def momentScalarGrow2622K07P020Input : RatPair2542 := (momentPanelGrowth2622K07P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P020Expected : RatState2542 :=
  ((((5819889199491024736912676620730947419644809511027725373271145114468333607842756879956987241830719 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((14755148215572399648181662882685105306167688920201 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P020_replay :
    compactExp2620 momentScalarGrow2622K07P020Input 20 = momentScalarGrow2622K07P020Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P020_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P020] using h

theorem momentScalarGrow2622K07P020_radius_le :
    (momentScalarGrow2622K07P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P020Expected]

end ConnesWeilRH.Dev
