import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P008 : ℚ := ((-822758362716125083180862614823898393119 : ℚ) / 9080434779554852848801184400749363200)

def momentPanelGrowth2622K13P008 : ℚ := ((1042985305672218520326419159969321758603 : ℚ) / 226744155802583301753954703664322969600)

theorem momentPanelPhase_owner2622K13P008 :
    (momentPanelPhase2622K13P008 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P008 :
    (momentPanelGrowth2622K13P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P008Input : RatPair2542 := (momentPanelPhase2622K13P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P008Expected : RatState2542 :=
  ((((476534291532532281459283165946001929786706005198716317969 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614629778888431 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K13P008_replay :
    compactExp2620 momentScalarAmp2622K13P008Input 20 = momentScalarAmp2622K13P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K13P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P008_replay] at h
  simpa only [momentPanelPhase_owner2622K13P008] using h

theorem momentScalarAmp2622K13P008_radius_le :
    (momentScalarAmp2622K13P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P008Expected]

def momentScalarGrow2622K13P008Input : RatPair2542 := (momentPanelGrowth2622K13P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P008Expected : RatState2542 :=
  ((((212461776191752688650118771605211850084131444537108142847770932079173403830737391546402478025406283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((134663058324015027825381086334668559768966043401045 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K13P008_replay :
    compactExp2620 momentScalarGrow2622K13P008Input 20 = momentScalarGrow2622K13P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P008] using h

theorem momentScalarGrow2622K13P008_radius_le :
    (momentScalarGrow2622K13P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P008Expected]

end ConnesWeilRH.Dev
