import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P132 : ℚ := ((-152571 : ℚ) / 4370)

def momentPanelGrowth2622K06P132 : ℚ := ((237146267 : ℚ) / 553656675)

theorem momentPanelPhase_owner2622K06P132 :
    (momentPanelPhase2622K06P132 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P132 :
    (momentPanelGrowth2622K06P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P132Input : RatPair2542 := (momentPanelPhase2622K06P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P132Expected : RatState2542 :=
  ((((183597648937718737839775288218412497344044644458051299679004221288081160506607665 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1861963356125955332813596683080543 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P132_replay :
    compactExp2620 momentScalarAmp2622K06P132Input 20 = momentScalarAmp2622K06P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K06P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P132_replay] at h
  simpa only [momentPanelPhase_owner2622K06P132] using h

theorem momentScalarAmp2622K06P132_radius_le :
    (momentScalarAmp2622K06P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P132Expected]

def momentScalarGrow2622K06P132Input : RatPair2542 := (momentPanelGrowth2622K06P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P132Expected : RatState2542 :=
  ((((1639037153778388236583871705173614561061003030928676711357838310831976818012280776608935940919585 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4155451166128340875059426470124773179079630144149 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P132_replay :
    compactExp2620 momentScalarGrow2622K06P132Input 20 = momentScalarGrow2622K06P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P132] using h

theorem momentScalarGrow2622K06P132_radius_le :
    (momentScalarGrow2622K06P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P132Expected]

end ConnesWeilRH.Dev
