import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P045 : ℚ := ((-28608184448930911843921231617601151870623508237739821 : ℚ) / 763077978905241450407812593566172574667035482521600)

def momentPanelGrowth2622K01P045 : ℚ := ((1548188634595635930348009471456512536898059162176753 : ℚ) / 3630953811436279586409305963428751864336116980121600)

theorem momentPanelPhase_owner2622K01P045 :
    (momentPanelPhase2622K01P045 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P045 :
    (momentPanelGrowth2622K01P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P045Input : RatPair2542 := (momentPanelPhase2622K01P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P045Expected : RatState2542 :=
  ((((55801509483093692460655032970761707511250195132467289191594342164553304900545233 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((70739347349702593088745134849179 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P045_replay :
    compactExp2620 momentScalarAmp2622K01P045Input 20 = momentScalarAmp2622K01P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K01P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P045_replay] at h
  simpa only [momentPanelPhase_owner2622K01P045] using h

theorem momentScalarAmp2622K01P045_radius_le :
    (momentScalarAmp2622K01P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P045Expected]

def momentScalarGrow2622K01P045Input : RatPair2542 := (momentPanelGrowth2622K01P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P045Expected : RatState2542 :=
  ((((1635858726184007390560778634867176198233138587415536859794246893669590354350055022159686125653147 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((518424113225241305056188859979763225312528775879 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P045_replay :
    compactExp2620 momentScalarGrow2622K01P045Input 20 = momentScalarGrow2622K01P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P045] using h

theorem momentScalarGrow2622K01P045_radius_le :
    (momentScalarGrow2622K01P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P045Expected]

end ConnesWeilRH.Dev
