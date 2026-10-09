import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P124 : ℚ := ((-89392332789278282216368268992428992175 : ℚ) / 2858927328092324856277908752271671296)

def momentPanelGrowth2622K07P124 : ℚ := ((588822093869467839003865828936740425 : ℚ) / 1665875430386326298600483537125638144)

theorem momentPanelPhase_owner2622K07P124 :
    (momentPanelPhase2622K07P124 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (69 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P124, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P124 :
    (momentPanelGrowth2622K07P124 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P124, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P124Input : RatPair2542 := (momentPanelPhase2622K07P124 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P124Expected : RatState2542 :=
  ((((56256271657849795813034070254225910837572237694886485572224372349487255065606239831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((35657711539694814509481246533972809 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P124_replay :
    compactExp2620 momentScalarAmp2622K07P124Input 20 = momentScalarAmp2622K07P124Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P124_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (69 / 200) 0) -
      (momentScalarAmp2622K07P124Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P124]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P124 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P124 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P124Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P124_replay] at h
  simpa only [momentPanelPhase_owner2622K07P124] using h

theorem momentScalarAmp2622K07P124_radius_le :
    (momentScalarAmp2622K07P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P124Expected]

def momentScalarGrow2622K07P124Input : RatPair2542 := (momentPanelGrowth2622K07P124 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P124Expected : RatState2542 :=
  ((((1520809456442777033850727169770894349527610666286297575397277698180440551867899926211068840454789 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((120490898152388188289209740629917876046045226333 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P124_replay :
    compactExp2620 momentScalarGrow2622K07P124Input 20 = momentScalarGrow2622K07P124Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P124_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P124Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P124]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P124 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P124 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P124Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P124_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P124] using h

theorem momentScalarGrow2622K07P124_radius_le :
    (momentScalarGrow2622K07P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P124Expected]

end ConnesWeilRH.Dev
