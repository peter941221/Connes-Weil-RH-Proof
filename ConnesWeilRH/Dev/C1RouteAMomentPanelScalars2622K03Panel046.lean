import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P046 : ℚ := ((-219988198231851623906900911262840861299400324896872225 : ℚ) / 5924744950034814067532962851227721826307693537656832)

def momentPanelGrowth2622K03P046 : ℚ := ((49419387941345619377107464741682046497045048586275 : ℚ) / 120847916636799035048967189605227652187799922147328)

theorem momentPanelPhase_owner2622K03P046 :
    (momentPanelPhase2622K03P046 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P046 :
    (momentPanelGrowth2622K03P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P046Input : RatPair2542 := (momentPanelPhase2622K03P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P046Expected : RatState2542 :=
  ((((79990284715369777203041645923931679050785428721251950567593792699830547772169217 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((101403324300994607812916419185911 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P046_replay :
    compactExp2620 momentScalarAmp2622K03P046Input 20 = momentScalarAmp2622K03P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K03P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P046_replay] at h
  simpa only [momentPanelPhase_owner2622K03P046] using h

theorem momentScalarAmp2622K03P046_radius_le :
    (momentScalarAmp2622K03P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P046Expected]

def momentScalarGrow2622K03P046Input : RatPair2542 := (momentPanelGrowth2622K03P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P046Expected : RatState2542 :=
  ((((1607564586841193701559645627683413629851414052831896780562651356367816705187342158198218360871023 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2037829418672832470327518692700993153615992156335 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P046_replay :
    compactExp2620 momentScalarGrow2622K03P046Input 20 = momentScalarGrow2622K03P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P046] using h

theorem momentScalarGrow2622K03P046_radius_le :
    (momentScalarGrow2622K03P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P046Expected]

end ConnesWeilRH.Dev
