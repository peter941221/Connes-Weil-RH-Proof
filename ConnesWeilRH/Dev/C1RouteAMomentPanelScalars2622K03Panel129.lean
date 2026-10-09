import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P129 : ℚ := ((-72834693529553835729683165383198406629802553048524525 : ℚ) / 2055784740610581317318258177819541602523526113263616)

def momentPanelGrowth2622K03P129 : ℚ := ((4606942450501099226689724495777901234634581795275 : ℚ) / 13427546292977670560996354400580850243088880238592)

theorem momentPanelPhase_owner2622K03P129 :
    (momentPanelPhase2622K03P129 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P129 :
    (momentPanelGrowth2622K03P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P129Input : RatPair2542 := (momentPanelPhase2622K03P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P129Expected : RatState2542 :=
  ((((438416505044000529729121013136995605584933449764249896607253506558022253580822571 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((555777725203188898297348204591857 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P129_replay :
    compactExp2620 momentScalarAmp2622K03P129Input 20 = momentScalarAmp2622K03P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K03P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P129_replay] at h
  simpa only [momentPanelPhase_owner2622K03P129] using h

theorem momentScalarAmp2622K03P129_radius_le :
    (momentScalarAmp2622K03P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P129Expected]

def momentScalarGrow2622K03P129Input : RatPair2542 := (momentPanelGrowth2622K03P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P129Expected : RatState2542 :=
  ((((1505128152315563803199657911257387989069544732038497406511375711692834939693607226243521301965989 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1907975981409188932972244259293219807170420164821 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P129_replay :
    compactExp2620 momentScalarGrow2622K03P129Input 20 = momentScalarGrow2622K03P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P129] using h

theorem momentScalarGrow2622K03P129_radius_le :
    (momentScalarGrow2622K03P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P129Expected]

end ConnesWeilRH.Dev
