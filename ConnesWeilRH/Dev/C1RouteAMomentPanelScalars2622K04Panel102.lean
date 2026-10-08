import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P102 : ℚ := ((-7023672876671754474575467007747780092159458965813 : ℚ) / 239777612374601260017792042867515182912301432832)

def momentPanelGrowth2622K04P102 : ℚ := ((806517325037243220859348759929465223407829763099216549 : ℚ) / 4598047856353373954267149869126122236929706881240268800)

theorem momentPanelPhase_owner2622K04P102 :
    (momentPanelPhase2622K04P102 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 8) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P102, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P102 :
    (momentPanelGrowth2622K04P102 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P102, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P102Input : RatPair2542 := (momentPanelPhase2622K04P102 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P102Expected : RatState2542 :=
  ((((405555921056177889773139430582852536509964369605396593643620792899662887706913606103 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((257058784331206311456733426650800975 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P102_replay :
    compactExp2620 momentScalarAmp2622K04P102Input 20 = momentScalarAmp2622K04P102Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P102_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 8) 0) -
      (momentScalarAmp2622K04P102Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P102]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P102 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P102 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P102Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P102_replay] at h
  simpa only [momentPanelPhase_owner2622K04P102] using h

theorem momentScalarAmp2622K04P102_radius_le :
    (momentScalarAmp2622K04P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P102Expected]

def momentScalarGrow2622K04P102Input : RatPair2542 := (momentPanelGrowth2622K04P102 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P102Expected : RatState2542 :=
  ((((1272757698340641028787878208308531710682301640624207851466252388732009314179962211612365482720115 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((806705895178688869757578860627453082015573177073 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P102_replay :
    compactExp2620 momentScalarGrow2622K04P102Input 20 = momentScalarGrow2622K04P102Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P102_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P102Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P102]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P102 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P102 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P102Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P102_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P102] using h

theorem momentScalarGrow2622K04P102_radius_le :
    (momentScalarGrow2622K04P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P102Expected]

end ConnesWeilRH.Dev
