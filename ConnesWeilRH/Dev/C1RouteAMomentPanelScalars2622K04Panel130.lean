import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P130 : ℚ := ((-305930651803163954395292461665612423277481430409087407 : ℚ) / 9545147119278918492541604906484333573100532871987200)

def momentPanelGrowth2622K04P130 : ℚ := ((1482137371924090447529436765740051091116207119445631349 : ℚ) / 3292458756973670093470272195712502065972225579470028800)

theorem momentPanelPhase_owner2622K04P130 :
    (momentPanelPhase2622K04P130 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (81 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P130, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P130 :
    (momentPanelGrowth2622K04P130 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P130, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P130Input : RatPair2542 := (momentPanelPhase2622K04P130 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P130Expected : RatState2542 :=
  ((((3213477383185157407682773860949122190544644540459963924657763307656231547200406381 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((32589528391862924209627013523603811 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P130_replay :
    compactExp2620 momentScalarAmp2622K04P130Input 20 = momentScalarAmp2622K04P130Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P130_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (81 / 200) 0) -
      (momentScalarAmp2622K04P130Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P130]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P130 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P130 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P130Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P130_replay] at h
  simpa only [momentPanelPhase_owner2622K04P130] using h

theorem momentScalarAmp2622K04P130_radius_le :
    (momentScalarAmp2622K04P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P130Expected]

def momentScalarGrow2622K04P130Input : RatPair2542 := (momentPanelGrowth2622K04P130 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P130Expected : RatState2542 :=
  ((((1675217366614593153459503478004588370782067292877296298186721235963436996328540469051112122734889 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4247178777258543159529794964458324173334968685609 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P130_replay :
    compactExp2620 momentScalarGrow2622K04P130Input 20 = momentScalarGrow2622K04P130Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P130_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P130Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P130]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P130 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P130 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P130Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P130_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P130] using h

theorem momentScalarGrow2622K04P130_radius_le :
    (momentScalarGrow2622K04P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P130Expected]

end ConnesWeilRH.Dev
