import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P064 : ℚ := ((-61907349 : ℚ) / 1869950)

def momentPanelGrowth2622K06P064 : ℚ := ((9936187 : ℚ) / 45279675)

theorem momentPanelPhase_owner2622K06P064 :
    (momentPanelPhase2622K06P064 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P064 :
    (momentPanelGrowth2622K06P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P064Input : RatPair2542 := (momentPanelPhase2622K06P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P064Expected : RatState2542 :=
  ((((4473354806504113958513271051417533286664988707633468337906151935129451427355992123 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((11341659895063205478306913525521895 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P064_replay :
    compactExp2620 momentScalarAmp2622K06P064Input 20 = momentScalarAmp2622K06P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K06P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P064_replay] at h
  simpa only [momentPanelPhase_owner2622K06P064] using h

theorem momentScalarAmp2622K06P064_radius_le :
    (momentScalarAmp2622K06P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P064Expected]

def momentScalarGrow2622K06P064Input : RatPair2542 := (momentPanelGrowth2622K06P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P064Expected : RatState2542 :=
  ((((1330057274811721173519463724130963141230952315025259218905484887438634362480764903480002740568247 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((843023774953010193715267307950738239100804354033 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P064_replay :
    compactExp2620 momentScalarGrow2622K06P064Input 20 = momentScalarGrow2622K06P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P064] using h

theorem momentScalarGrow2622K06P064_radius_le :
    (momentScalarGrow2622K06P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P064Expected]

end ConnesWeilRH.Dev
