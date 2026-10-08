import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P110 : ℚ := ((-107101598035962428881788517469769905326805069826659789 : ℚ) / 3646046955786645112151497337555680275403364525670400)

def momentPanelGrowth2622K04P110 : ℚ := ((3033346575626120144775096331960388682683472231251969487 : ℚ) / 13041401717945456973852261120802947379899769012250214400)

theorem momentPanelPhase_owner2622K04P110 :
    (momentPanelPhase2622K04P110 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (41 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P110, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P110 :
    (momentPanelGrowth2622K04P110 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P110, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P110Input : RatPair2542 := (momentPanelPhase2622K04P110 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P110Expected : RatState2542 :=
  ((((373526180917132383381589502150032600439762694866942662003587138990945655441732962329 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((236756976117990529039847743050904231 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P110_replay :
    compactExp2620 momentScalarAmp2622K04P110Input 20 = momentScalarAmp2622K04P110Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P110_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (41 / 200) 0) -
      (momentScalarAmp2622K04P110Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P110]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P110 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P110 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P110Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P110_replay] at h
  simpa only [momentPanelPhase_owner2622K04P110] using h

theorem momentScalarAmp2622K04P110_radius_le :
    (momentScalarAmp2622K04P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P110Expected]

def momentScalarGrow2622K04P110Input : RatPair2542 := (momentPanelGrowth2622K04P110 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P110Expected : RatState2542 :=
  ((((1347667433867310239025304679757697216982530473941946442631176834644930406127578245909222269499855 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3416742105003028945645257447618666097945107979371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P110_replay :
    compactExp2620 momentScalarGrow2622K04P110Input 20 = momentScalarGrow2622K04P110Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P110_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P110Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P110]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P110 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P110 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P110Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P110_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P110] using h

theorem momentScalarGrow2622K04P110_radius_le :
    (momentScalarGrow2622K04P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P110Expected]

end ConnesWeilRH.Dev
