import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P163 : ℚ := ((-57296523 : ℚ) / 919550)

def momentPanelGrowth2622K06P163 : ℚ := ((23551387 : ℚ) / 10659675)

theorem momentPanelPhase_owner2622K06P163 :
    (momentPanelPhase2622K06P163 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P163 :
    (momentPanelGrowth2622K06P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P163Input : RatPair2542 := (momentPanelPhase2622K06P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P163Expected : RatState2542 :=
  ((((1857849500822759139233775137340490119621967177373400994449833162404915 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2420206883215252637515537 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P163_replay :
    compactExp2620 momentScalarAmp2622K06P163Input 20 = momentScalarAmp2622K06P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K06P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P163_replay] at h
  simpa only [momentPanelPhase_owner2622K06P163] using h

theorem momentScalarAmp2622K06P163_radius_le :
    (momentScalarAmp2622K06P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P163Expected]

def momentScalarGrow2622K06P163Input : RatPair2542 := (momentPanelGrowth2622K06P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P163Expected : RatState2542 :=
  ((((9729596143503850035451077905110854073586526533790486731493130097856950385933933147476634865309797 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1541712800458664191712076417334198621637117552581 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P163_replay :
    compactExp2620 momentScalarGrow2622K06P163Input 20 = momentScalarGrow2622K06P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P163] using h

theorem momentScalarGrow2622K06P163_radius_le :
    (momentScalarGrow2622K06P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P163Expected]

end ConnesWeilRH.Dev
