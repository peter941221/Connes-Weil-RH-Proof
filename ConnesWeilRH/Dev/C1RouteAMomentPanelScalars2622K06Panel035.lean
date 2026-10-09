import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P035 : ℚ := ((-21021657 : ℚ) / 468650)

def momentPanelGrowth2622K06P035 : ℚ := ((465947 : ℚ) / 648675)

theorem momentPanelPhase_owner2622K06P035 :
    (momentPanelPhase2622K06P035 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P035 :
    (momentPanelGrowth2622K06P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P035Input : RatPair2542 := (momentPanelPhase2622K06P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P035Expected : RatState2542 :=
  ((((35314646502066159292177218017314764187099388894944501779215681832335374290787 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((44769756819885856255180619099 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P035_replay :
    compactExp2620 momentScalarAmp2622K06P035Input 20 = momentScalarAmp2622K06P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K06P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P035_replay] at h
  simpa only [momentPanelPhase_owner2622K06P035] using h

theorem momentScalarAmp2622K06P035_radius_le :
    (momentScalarAmp2622K06P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P035Expected]

def momentScalarGrow2622K06P035Input : RatPair2542 := (momentPanelGrowth2622K06P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P035Expected : RatState2542 :=
  ((((547601792189996170301319080588876475081490917664361973245565081306071345542380248749919910665921 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((5553338120242378594567567604906096665327964243121 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P035_replay :
    compactExp2620 momentScalarGrow2622K06P035Input 20 = momentScalarGrow2622K06P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P035] using h

theorem momentScalarGrow2622K06P035_radius_le :
    (momentScalarGrow2622K06P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P035Expected]

end ConnesWeilRH.Dev
