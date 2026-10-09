import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P019 : ℚ := ((-62836779 : ℚ) / 1005950)

def momentPanelGrowth2622K06P019 : ℚ := ((363197227 : ℚ) / 204930675)

theorem momentPanelPhase_owner2622K06P019 :
    (momentPanelPhase2622K06P019 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P019 :
    (momentPanelGrowth2622K06P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P019Input : RatPair2542 := (momentPanelPhase2622K06P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P019Expected : RatState2542 :=
  ((((794905210088606138878181514514585121410037155286408564674119438324939 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2419867083421977864980915 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P019_replay :
    compactExp2620 momentScalarAmp2622K06P019Input 20 = momentScalarAmp2622K06P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K06P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P019_replay] at h
  simpa only [momentPanelPhase_owner2622K06P019] using h

theorem momentScalarAmp2622K06P019_radius_le :
    (momentScalarAmp2622K06P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P019Expected]

def momentScalarGrow2622K06P019Input : RatPair2542 := (momentPanelGrowth2622K06P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P019Expected : RatState2542 :=
  ((((6284427821167183168397083189014767484880261846045552520331204209602515756225818686309686640887413 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3983222617386315109996058043831810823410484117821 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P019_replay :
    compactExp2620 momentScalarGrow2622K06P019Input 20 = momentScalarGrow2622K06P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P019] using h

theorem momentScalarGrow2622K06P019_radius_le :
    (momentScalarGrow2622K06P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P019Expected]

end ConnesWeilRH.Dev
