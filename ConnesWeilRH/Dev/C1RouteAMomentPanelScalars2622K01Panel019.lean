import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P019 : ℚ := ((-85823340661378983378466164693729933272508049372604667 : ℚ) / 1435739816477560342350582770967719632444223966412800)

def momentPanelGrowth2622K01P019 : ℚ := ((507217564792717188978773551439896891393370430049574971 : ℚ) / 292486833058424934948194258062314416708133324010291200)

theorem momentPanelPhase_owner2622K01P019 :
    (momentPanelPhase2622K01P019 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P019 :
    (momentPanelGrowth2622K01P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P019Input : RatPair2542 := (momentPanelPhase2622K01P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P019Expected : RatState2542 :=
  ((((23390691323520372012664069433749907510620606681770429226161112559762705 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1223752276753696912228109 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P019_replay :
    compactExp2620 momentScalarAmp2622K01P019Input 20 = momentScalarAmp2622K01P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K01P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P019_replay] at h
  simpa only [momentPanelPhase_owner2622K01P019] using h

theorem momentScalarAmp2622K01P019_radius_le :
    (momentScalarAmp2622K01P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P019Expected]

def momentScalarGrow2622K01P019Input : RatPair2542 := (momentPanelGrowth2622K01P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P019Expected : RatState2542 :=
  ((((6049265617283408699569099360338678321445556093506413348670433361865048137986447355389280755142195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((958542813578263969549319969376451386998436411193 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K01P019_replay :
    compactExp2620 momentScalarGrow2622K01P019Input 20 = momentScalarGrow2622K01P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P019] using h

theorem momentScalarGrow2622K01P019_radius_le :
    (momentScalarGrow2622K01P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P019Expected]

end ConnesWeilRH.Dev
