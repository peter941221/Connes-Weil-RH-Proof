import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P143 : ℚ := ((-29116818641781772297010848142000812075 : ℚ) / 772110768791811789698823961956057088)

def momentPanelGrowth2622K07P143 : ℚ := ((92415732527659018656566561808520179075 : ℚ) / 127229162119373697672311081541526618112)

theorem momentPanelPhase_owner2622K07P143 :
    (momentPanelPhase2622K07P143 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P143 :
    (momentPanelGrowth2622K07P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P143Input : RatPair2542 := (momentPanelPhase2622K07P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P143Expected : RatState2542 :=
  ((((22387229344084986466936655872620554890147795283177279076887502939969227802804367 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((28380205958853162721307993400235 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P143_replay :
    compactExp2620 momentScalarAmp2622K07P143Input 20 = momentScalarAmp2622K07P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K07P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P143_replay] at h
  simpa only [momentPanelPhase_owner2622K07P143] using h

theorem momentScalarAmp2622K07P143_radius_le :
    (momentScalarAmp2622K07P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P143Expected]

def momentScalarGrow2622K07P143Input : RatPair2542 := (momentPanelGrowth2622K07P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P143Expected : RatState2542 :=
  ((((276018434931151084779100460001030593016664687464852688979660007605820948748375598806020082585055 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2799157538676001260324431283162793137719488917455 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P143_replay :
    compactExp2620 momentScalarGrow2622K07P143Input 20 = momentScalarGrow2622K07P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P143] using h

theorem momentScalarGrow2622K07P143_radius_le :
    (momentScalarGrow2622K07P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P143Expected]

end ConnesWeilRH.Dev
