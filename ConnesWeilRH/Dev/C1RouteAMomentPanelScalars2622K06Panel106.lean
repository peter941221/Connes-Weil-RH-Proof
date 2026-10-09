import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P106 : ℚ := ((-58715937 : ℚ) / 1945550)

def momentPanelGrowth2622K06P106 : ℚ := ((116434507 : ℚ) / 785862675)

theorem momentPanelPhase_owner2622K06P106 :
    (momentPanelPhase2622K06P106 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P106 :
    (momentPanelGrowth2622K06P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P106Input : RatPair2542 := (momentPanelPhase2622K06P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P106Expected : RatState2542 :=
  ((((83508609066150576581798320865563446833393498187138706570043079488178321640958449999 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((105862785255883150465746390236676395 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P106_replay :
    compactExp2620 momentScalarAmp2622K06P106Input 20 = momentScalarAmp2622K06P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K06P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P106_replay] at h
  simpa only [momentPanelPhase_owner2622K06P106] using h

theorem momentScalarAmp2622K06P106_radius_le :
    (momentScalarAmp2622K06P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P106Expected]

def momentScalarGrow2622K06P106Input : RatPair2542 := (momentPanelGrowth2622K06P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P106Expected : RatState2542 :=
  ((((619276066122844915696976391345078213299453861832352599716363440269643353805331584839433923458477 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((196256391501318983130261332275500757582896288433 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P106_replay :
    compactExp2620 momentScalarGrow2622K06P106Input 20 = momentScalarGrow2622K06P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P106] using h

theorem momentScalarGrow2622K06P106_radius_le :
    (momentScalarGrow2622K06P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P106Expected]

end ConnesWeilRH.Dev
