import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P153 : ℚ := ((-108283089974102621135721710311070419157088741461641019 : ℚ) / 2271321978172264554716156291781926560039502977433600)

def momentPanelGrowth2622K02P153 : ℚ := ((7401081955619700363335001404350947933966856228716773 : ℚ) / 6477849102884540112159242529540423575500372102348800)

theorem momentPanelPhase_owner2622K02P153 :
    (momentPanelPhase2622K02P153 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (127 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P153, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P153 :
    (momentPanelGrowth2622K02P153 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P153, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P153Input : RatPair2542 := (momentPanelPhase2622K02P153 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P153Expected : RatState2542 :=
  ((((2108613803666154512509283616422562689810650132054539627864883751143631887733 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2674316011088680025617146289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P153_replay :
    compactExp2620 momentScalarAmp2622K02P153Input 20 = momentScalarAmp2622K02P153Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P153_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (127 / 200) 0) -
      (momentScalarAmp2622K02P153Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P153]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P153 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P153 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P153Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P153_replay] at h
  simpa only [momentPanelPhase_owner2622K02P153] using h

theorem momentScalarAmp2622K02P153_radius_le :
    (momentScalarAmp2622K02P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P153Expected]

def momentScalarGrow2622K02P153Input : RatPair2542 := (momentPanelGrowth2622K02P153 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P153Expected : RatState2542 :=
  ((((3347799230469003508141619873532176556090516168244783278971134832375912168817080100777266447615833 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8487670159780656640574576552744766740122739327969 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P153_replay :
    compactExp2620 momentScalarGrow2622K02P153Input 20 = momentScalarGrow2622K02P153Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P153_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P153Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P153]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P153 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P153 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P153Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P153_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P153] using h

theorem momentScalarGrow2622K02P153_radius_le :
    (momentScalarGrow2622K02P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P153Expected]

end ConnesWeilRH.Dev
