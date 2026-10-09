import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P149 : ℚ := ((-28476855110049011983107224760898214081887289868937469 : ℚ) / 614644218863821622777750852743425080483229833625600)

def momentPanelGrowth2622K01P149 : ℚ := ((31426864170024536551798967127591702448569276273 : ℚ) / 35681192317648997026457149236237378409568665600)

theorem momentPanelPhase_owner2622K01P149 :
    (momentPanelPhase2622K01P149 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P149 :
    (momentPanelGrowth2622K01P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P149Input : RatPair2542 := (momentPanelPhase2622K01P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P149Expected : RatState2542 :=
  ((((2020090416749899830887298135052515796411909655062721322107043349139098291201 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((20489473673021255764614938309 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P149_replay :
    compactExp2620 momentScalarAmp2622K01P149Input 20 = momentScalarAmp2622K01P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K01P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P149_replay] at h
  simpa only [momentPanelPhase_owner2622K01P149] using h

theorem momentScalarAmp2622K01P149_radius_le :
    (momentScalarAmp2622K01P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P149Expected]

def momentScalarGrow2622K01P149Input : RatPair2542 := (momentPanelGrowth2622K01P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P149Expected : RatState2542 :=
  ((((2576804334591771250938222405652791150397439035404179169077530472532171891623403367319230719043245 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6532969635356364814461597093940195519916870347413 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P149_replay :
    compactExp2620 momentScalarGrow2622K01P149Input 20 = momentScalarGrow2622K01P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P149] using h

theorem momentScalarGrow2622K01P149_radius_le :
    (momentScalarGrow2622K01P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P149Expected]

end ConnesWeilRH.Dev
