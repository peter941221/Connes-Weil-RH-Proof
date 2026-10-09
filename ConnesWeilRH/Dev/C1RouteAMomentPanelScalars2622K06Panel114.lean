import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P114 : ℚ := ((-19385883 : ℚ) / 626650)

def momentPanelGrowth2622K06P114 : ℚ := ((79 : ℚ) / 375)

theorem momentPanelPhase_owner2622K06P114 :
    (momentPanelPhase2622K06P114 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (49 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P114, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P114 :
    (momentPanelGrowth2622K06P114 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P114, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P114Input : RatPair2542 := (momentPanelPhase2622K06P114 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P114Expected : RatState2542 :=
  ((((1225170139017785094918923274900592066231910814437834959769924205818840382108749915 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((99400542910791034326736274782063901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P114_replay :
    compactExp2620 momentScalarAmp2622K06P114Input 20 = momentScalarAmp2622K06P114Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P114_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (49 / 200) 0) -
      (momentScalarAmp2622K06P114Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P114]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P114 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P114 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P114Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P114_replay] at h
  simpa only [momentPanelPhase_owner2622K06P114] using h

theorem momentScalarAmp2622K06P114_radius_le :
    (momentScalarAmp2622K06P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P114Expected]

def momentScalarGrow2622K06P114Input : RatPair2542 := (momentPanelGrowth2622K06P114 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P114Expected : RatState2542 :=
  ((((1318438837587578678375593667476326247342441422734634151594935367691666980624492197343710604377919 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((835659724025821219620341146350167773919572090779 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P114_replay :
    compactExp2620 momentScalarGrow2622K06P114Input 20 = momentScalarGrow2622K06P114Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P114_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P114Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P114]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P114 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P114 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P114Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P114_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P114] using h

theorem momentScalarGrow2622K06P114_radius_le :
    (momentScalarGrow2622K06P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P114Expected]

end ConnesWeilRH.Dev
