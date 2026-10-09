import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P105 : ℚ := ((-28518151260761545862636048187985293245634296942522981 : ℚ) / 928638711259132796610573766022314010487434090905600)

def momentPanelGrowth2622K01P105 : ℚ := ((454228834479375198734383057967888676994730987882171 : ℚ) / 4411158762653992555389817988628318380639745422131200)

theorem momentPanelPhase_owner2622K01P105 :
    (momentPanelPhase2622K01P105 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P105 :
    (momentPanelGrowth2622K01P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P105Input : RatPair2542 := (momentPanelPhase2622K01P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P105Expected : RatState2542 :=
  ((((12288128921774508119448797320975921836213422450555994222303792116683851599147079133 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((124620081722445846422186798219908905 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P105_replay :
    compactExp2620 momentScalarAmp2622K01P105Input 20 = momentScalarAmp2622K01P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K01P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P105_replay] at h
  simpa only [momentPanelPhase_owner2622K01P105] using h

theorem momentScalarAmp2622K01P105_radius_le :
    (momentScalarAmp2622K01P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P105Expected]

def momentScalarGrow2622K01P105Input : RatPair2542 := (momentPanelGrowth2622K01P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P105Expected : RatState2542 :=
  ((((1183829295549851301667958154042172742657558523632319133122149232974293331714955346006421269183939 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3001363539401947472545490083657874352453345327455 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P105_replay :
    compactExp2620 momentScalarGrow2622K01P105Input 20 = momentScalarGrow2622K01P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P105] using h

theorem momentScalarGrow2622K01P105_radius_le :
    (momentScalarGrow2622K01P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P105Expected]

end ConnesWeilRH.Dev
