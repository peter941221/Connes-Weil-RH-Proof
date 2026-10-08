import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P081 : ℚ := ((-117221299986482053639093458785487565757868459893752283 : ℚ) / 3778495541669758189113706275520593424059683412377600)

def momentPanelGrowth2622K04P081 : ℚ := ((2100503279755158199808717625065224344188626009817575647 : ℚ) / 14042199218052417690129379708868688965492442006972006400)

theorem momentPanelPhase_owner2622K04P081 :
    (momentPanelPhase2622K04P081 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P081 :
    (momentPanelGrowth2622K04P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P081Input : RatPair2542 := (momentPanelPhase2622K04P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P081Expected : RatState2542 :=
  ((((35919658298016854953828751350078074990098312143412979275736284400554917266345264297 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((91069847167021072969242073619457101 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P081_replay :
    compactExp2620 momentScalarAmp2622K04P081Input 20 = momentScalarAmp2622K04P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K04P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P081_replay] at h
  simpa only [momentPanelPhase_owner2622K04P081] using h

theorem momentScalarAmp2622K04P081_radius_le :
    (momentScalarAmp2622K04P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P081Expected]

def momentScalarGrow2622K04P081Input : RatPair2542 := (momentPanelGrowth2622K04P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P081Expected : RatState2542 :=
  ((((1240316682320761654223889509962780424821938520198990839601293901616138000889516310986979536380649 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((786143981260780683902256715315873341951210735635 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P081_replay :
    compactExp2620 momentScalarGrow2622K04P081Input 20 = momentScalarGrow2622K04P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P081] using h

theorem momentScalarGrow2622K04P081_radius_le :
    (momentScalarGrow2622K04P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P081Expected]

end ConnesWeilRH.Dev
