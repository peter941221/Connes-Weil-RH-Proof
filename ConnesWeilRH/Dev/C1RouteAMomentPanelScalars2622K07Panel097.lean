import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P097 : ℚ := ((-3816063784624495825270197174372592125 : ℚ) / 129077254717639230578000307184205824)

def momentPanelGrowth2622K07P097 : ℚ := ((674526846776519566556380136156623025 : ℚ) / 5214485814641222555974294622126997504)

theorem momentPanelPhase_owner2622K07P097 :
    (momentPanelPhase2622K07P097 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P097, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P097 :
    (momentPanelGrowth2622K07P097 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P097, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P097Input : RatPair2542 := (momentPanelPhase2622K07P097 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P097Expected : RatState2542 :=
  ((((154527716921108734764760262268981036973787028896003112885506121521998748492620329027 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((24486584518328483438512388030765195 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K07P097_replay :
    compactExp2620 momentScalarAmp2622K07P097Input 20 = momentScalarAmp2622K07P097Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P097_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 40) 0) -
      (momentScalarAmp2622K07P097Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P097]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P097 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P097 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P097Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P097_replay] at h
  simpa only [momentPanelPhase_owner2622K07P097] using h

theorem momentScalarAmp2622K07P097_radius_le :
    (momentScalarAmp2622K07P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P097Expected]

def momentScalarGrow2622K07P097Input : RatPair2542 := (momentPanelGrowth2622K07P097 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P097Expected : RatState2542 :=
  ((((2430957470993444212063229179434100322630293104059747250928920894776869916855316444007008616259887 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3081604317075610767448017361875733812662790074839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P097_replay :
    compactExp2620 momentScalarGrow2622K07P097Input 20 = momentScalarGrow2622K07P097Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P097_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P097Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P097]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P097 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P097 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P097Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P097_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P097] using h

theorem momentScalarGrow2622K07P097_radius_le :
    (momentScalarGrow2622K07P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P097Expected]

end ConnesWeilRH.Dev
