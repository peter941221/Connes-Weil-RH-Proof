import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P077 : ℚ := ((-1301 : ℚ) / 42)

def momentPanelGrowth2622K06P077 : ℚ := ((97216187 : ℚ) / 805404675)

theorem momentPanelPhase_owner2622K06P077 :
    (momentPanelPhase2622K06P077 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P077 :
    (momentPanelGrowth2622K06P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P077Input : RatPair2542 := (momentPanelPhase2622K06P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P077Expected : RatState2542 :=
  ((((37651304055501352471353977152503821704950928042322478895797642222762623236423545373 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((47730108170255864770585725846923233 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P077_replay :
    compactExp2620 momentScalarAmp2622K06P077Input 20 = momentScalarAmp2622K06P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K06P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P077_replay] at h
  simpa only [momentPanelPhase_owner2622K06P077] using h

theorem momentScalarAmp2622K06P077_radius_le :
    (momentScalarAmp2622K06P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P077Expected]

def momentScalarGrow2622K06P077Input : RatPair2542 := (momentPanelGrowth2622K06P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P077Expected : RatState2542 :=
  ((((1205008284918744917116549574344303012779879476955848608413101703761130276439910927525258669743193 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((190941162477335571324099866267579999391013728799 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P077_replay :
    compactExp2620 momentScalarGrow2622K06P077Input 20 = momentScalarGrow2622K06P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P077] using h

theorem momentScalarGrow2622K06P077_radius_le :
    (momentScalarGrow2622K06P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P077Expected]

end ConnesWeilRH.Dev
