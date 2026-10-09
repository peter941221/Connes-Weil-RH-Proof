import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P160 : ℚ := ((-85446382463336202348528151640209483093421545507395333 : ℚ) / 1435739816477560342350582770967719632444223966412800)

def momentPanelGrowth2622K01P160 : ℚ := ((507217564792717188978773551439896891393370430049574971 : ℚ) / 292486833058424934948194258062314416708133324010291200)

theorem momentPanelPhase_owner2622K01P160 :
    (momentPanelPhase2622K01P160 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P160 :
    (momentPanelGrowth2622K01P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P160Input : RatPair2542 := (momentPanelPhase2622K01P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P160Expected : RatState2542 :=
  ((((15206823414484696093611582247662376995184026696514435371752198081199653 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((614101926286285340104399 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P160_replay :
    compactExp2620 momentScalarAmp2622K01P160Input 20 = momentScalarAmp2622K01P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K01P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P160_replay] at h
  simpa only [momentPanelPhase_owner2622K01P160] using h

theorem momentScalarAmp2622K01P160_radius_le :
    (momentScalarAmp2622K01P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P160Expected]

def momentScalarGrow2622K01P160Input : RatPair2542 := (momentPanelGrowth2622K01P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P160Expected : RatState2542 :=
  ((((6049265617283408699569099360338678321445556093506413348670433361865048137986447355389280755142195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((958542813578263969549319969376451386998436411193 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K01P160_replay :
    compactExp2620 momentScalarGrow2622K01P160Input 20 = momentScalarGrow2622K01P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P160] using h

theorem momentScalarGrow2622K01P160_radius_le :
    (momentScalarGrow2622K01P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P160Expected]

end ConnesWeilRH.Dev
