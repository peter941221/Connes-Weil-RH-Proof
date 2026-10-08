import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P156 : ℚ := ((-100810888480978806240083152559039568487352013135195233 : ℚ) / 2122888218130844727086094550959179065855697328537600)

def momentPanelGrowth2622K04P156 : ℚ := ((2049343599393588072530216554262945461176887596915039589 : ℚ) / 1444903745738117498958893707691764005866396667661516800)

theorem momentPanelPhase_owner2622K04P156 :
    (momentPanelPhase2622K04P156 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P156 :
    (momentPanelGrowth2622K04P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P156Input : RatPair2542 := (momentPanelPhase2622K04P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P156Expected : RatState2542 :=
  ((((5081494811990890520801295222373744917851471426605026452407139876997129092451 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6444269530248925976062377549 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P156_replay :
    compactExp2620 momentScalarAmp2622K04P156Input 20 = momentScalarAmp2622K04P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K04P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P156_replay] at h
  simpa only [momentPanelPhase_owner2622K04P156] using h

theorem momentScalarAmp2622K04P156_radius_le :
    (momentScalarAmp2622K04P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P156Expected]

def momentScalarGrow2622K04P156Input : RatPair2542 := (momentPanelGrowth2622K04P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P156Expected : RatState2542 :=
  ((((4411024666886536613932905602529866189905340885505528461706858045734020750939315548789040039565407 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((698953812905169439625192918479316177553302310265 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K04P156_replay :
    compactExp2620 momentScalarGrow2622K04P156Input 20 = momentScalarGrow2622K04P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P156] using h

theorem momentScalarGrow2622K04P156_radius_le :
    (momentScalarGrow2622K04P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P156Expected]

end ConnesWeilRH.Dev
