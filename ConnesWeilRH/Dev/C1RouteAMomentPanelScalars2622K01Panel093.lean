import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P093 : ℚ := ((-28538760268671873383918159455904505020388299301347213 : ℚ) / 950332876188263386802659712757946336560451839590400)

def momentPanelGrowth2622K01P093 : ℚ := ((469247135596361047053401693999394959621328350411 : ℚ) / 18090364505048041492413774662772350853651313459200)

theorem momentPanelPhase_owner2622K01P093 :
    (momentPanelPhase2622K01P093 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P093 :
    (momentPanelGrowth2622K01P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P093Input : RatPair2542 := (momentPanelPhase2622K01P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P093Expected : RatState2542 :=
  ((((96958230478523750386064794488171550777664228199799335486048328650201906154794151155 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15364084890381304077653328676713225 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K01P093_replay :
    compactExp2620 momentScalarAmp2622K01P093Input 20 = momentScalarAmp2622K01P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K01P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P093_replay] at h
  simpa only [momentPanelPhase_owner2622K01P093] using h

theorem momentScalarAmp2622K01P093_radius_le :
    (momentScalarAmp2622K01P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P093Expected]

def momentScalarGrow2622K01P093Input : RatPair2542 := (momentPanelGrowth2622K01P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P093Expected : RatState2542 :=
  ((((2192117379004748407313493688653549767752895119188987006927719802174815038786372364537437881226433 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((173677427657799908159200635396432613868585421497 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K01P093_replay :
    compactExp2620 momentScalarGrow2622K01P093Input 20 = momentScalarGrow2622K01P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P093] using h

theorem momentScalarGrow2622K01P093_radius_le :
    (momentScalarGrow2622K01P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P093Expected]

end ConnesWeilRH.Dev
