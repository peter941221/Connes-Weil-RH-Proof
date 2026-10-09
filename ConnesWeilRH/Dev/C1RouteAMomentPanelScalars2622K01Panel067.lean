import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P067 : ℚ := ((-685987210616952222621462626101379180992120767288183 : ℚ) / 21679892452203530593275363875937831121653921218560)

def momentPanelGrowth2622K01P067 : ℚ := ((166120074054066301001301121595167014662430636753937531 : ℚ) / 1066865759194512175694226359934588093865047394300723200)

theorem momentPanelPhase_owner2622K01P067 :
    (momentPanelPhase2622K01P067 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P067 :
    (momentPanelGrowth2622K01P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P067Input : RatPair2542 := (momentPanelPhase2622K01P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P067Expected : RatState2542 :=
  ((((38708986322792243619868359724873059268378057552469135642596256013289437547091539607 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((766733601284752444245954654118559 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K01P067_replay :
    compactExp2620 momentScalarAmp2622K01P067Input 20 = momentScalarAmp2622K01P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K01P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P067_replay] at h
  simpa only [momentPanelPhase_owner2622K01P067] using h

theorem momentScalarAmp2622K01P067_radius_le :
    (momentScalarAmp2622K01P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P067Expected]

def momentScalarGrow2622K01P067Input : RatPair2542 := (momentPanelGrowth2622K01P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P067Expected : RatState2542 :=
  ((((2495869981248956373948014094093573391009678644189085056359569955667768737524752502850639719142677 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1581945304999622132305575560364350108622291794891 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P067_replay :
    compactExp2620 momentScalarGrow2622K01P067Input 20 = momentScalarGrow2622K01P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P067] using h

theorem momentScalarGrow2622K01P067_radius_le :
    (momentScalarGrow2622K01P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P067Expected]

end ConnesWeilRH.Dev
