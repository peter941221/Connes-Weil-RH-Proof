import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P142 : ℚ := ((-683461779290154099301326676814474506481508905751453 : ℚ) / 16541800758462075021465534385919648630676033372160)

def momentPanelGrowth2622K01P142 : ℚ := ((379365874633388227085914052736506351631581139270985771 : ℚ) / 615030539133044808468556304298205822579270233568051200)

theorem momentPanelPhase_owner2622K01P142 :
    (momentPanelPhase2622K01P142 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P142 :
    (momentPanelGrowth2622K01P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P142Input : RatPair2542 := (momentPanelPhase2622K01P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P142Expected : RatState2542 :=
  ((((1215383424702134797429988969464158012335541160503344417950666703044064810443577 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3081486891482174175573516407371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P142_replay :
    compactExp2620 momentScalarAmp2622K01P142Input 20 = momentScalarAmp2622K01P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K01P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P142_replay] at h
  simpa only [momentPanelPhase_owner2622K01P142] using h

theorem momentScalarAmp2622K01P142_radius_le :
    (momentScalarAmp2622K01P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P142Expected]

def momentScalarGrow2622K01P142Input : RatPair2542 := (momentPanelGrowth2622K01P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P142Expected : RatState2542 :=
  ((((1979028607737047989994779470844630378081111401751092118838688542653527602349283516406792810745777 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1254357663357696347585328989471517047513255078787 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P142_replay :
    compactExp2620 momentScalarGrow2622K01P142Input 20 = momentScalarGrow2622K01P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P142] using h

theorem momentScalarGrow2622K01P142_radius_le :
    (momentScalarGrow2622K01P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P142Expected]

end ConnesWeilRH.Dev
