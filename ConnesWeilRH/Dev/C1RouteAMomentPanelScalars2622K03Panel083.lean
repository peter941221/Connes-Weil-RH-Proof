import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P083 : ℚ := ((-73121754390837443917314454183666628118087840837843425 : ℚ) / 2425544654855299755623790440496761206496477046636544)

def momentPanelGrowth2622K03P083 : ℚ := ((136806844482754749976493464028291185395781092551269475 : ℚ) / 3015029191540359134550739149642702008372096547906650112)

theorem momentPanelPhase_owner2622K03P083 :
    (momentPanelPhase2622K03P083 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P083 :
    (momentPanelGrowth2622K03P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P083Input : RatPair2542 := (momentPanelPhase2622K03P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P083Expected : RatState2542 :=
  ((((2697410644737941554084057323694227125751367812312789836150573688109657617579584537 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((54711560499610834931483527519911319 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P083_replay :
    compactExp2620 momentScalarAmp2622K03P083Input 20 = momentScalarAmp2622K03P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K03P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P083_replay] at h
  simpa only [momentPanelPhase_owner2622K03P083] using h

theorem momentScalarAmp2622K03P083_radius_le :
    (momentScalarAmp2622K03P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P083Expected]

def momentScalarGrow2622K03P083Input : RatPair2542 := (momentPanelGrowth2622K03P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P083Expected : RatState2542 :=
  ((((279392486303105029442483373354782457817935309954688320056123461958802811115631212241638538554191 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((708344075270646387858213610992302979085881505577 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P083_replay :
    compactExp2620 momentScalarGrow2622K03P083Input 20 = momentScalarGrow2622K03P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P083] using h

theorem momentScalarGrow2622K03P083_radius_le :
    (momentScalarGrow2622K03P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P083Expected]

end ConnesWeilRH.Dev
