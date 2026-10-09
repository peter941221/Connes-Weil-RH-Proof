import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P073 : ℚ := ((-61284063 : ℚ) / 1945550)

def momentPanelGrowth2622K06P073 : ℚ := ((116434507 : ℚ) / 785862675)

theorem momentPanelPhase_owner2622K06P073 :
    (momentPanelPhase2622K06P073 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P073 :
    (momentPanelGrowth2622K06P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P073Input : RatPair2542 := (momentPanelPhase2622K06P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P073Expected : RatState2542 :=
  ((((22308097499634284149785731850676917791262855687315221149991294783077722357441652755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((56559445414143158878940927083911607 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P073_replay :
    compactExp2620 momentScalarAmp2622K06P073Input 20 = momentScalarAmp2622K06P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K06P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P073_replay] at h
  simpa only [momentPanelPhase_owner2622K06P073] using h

theorem momentScalarAmp2622K06P073_radius_le :
    (momentScalarAmp2622K06P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P073Expected]

def momentScalarGrow2622K06P073Input : RatPair2542 := (momentPanelGrowth2622K06P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P073Expected : RatState2542 :=
  ((((619276066122844915696976391345078213299453861832352599716363440269643353805331584839433923458477 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((196256391501318983130261332275500757582896288433 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P073_replay :
    compactExp2620 momentScalarGrow2622K06P073Input 20 = momentScalarGrow2622K06P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P073] using h

theorem momentScalarGrow2622K06P073_radius_le :
    (momentScalarGrow2622K06P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P073Expected]

end ConnesWeilRH.Dev
