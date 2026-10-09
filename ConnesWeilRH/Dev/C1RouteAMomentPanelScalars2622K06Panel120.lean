import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P120 : ℚ := ((-19262327 : ℚ) / 604650)

def momentPanelGrowth2622K06P120 : ℚ := ((182234507 : ℚ) / 680862675)

theorem momentPanelPhase_owner2622K06P120 :
    (momentPanelPhase2622K06P120 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (61 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P120 :
    (momentPanelGrowth2622K06P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P120Input : RatPair2542 := (momentPanelPhase2622K06P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P120Expected : RatState2542 :=
  ((((3901171990874861781263535970837345063329520609082830946716708111048553255198488095 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((39563786105670384552537747431927433 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P120_replay :
    compactExp2620 momentScalarAmp2622K06P120Input 20 = momentScalarAmp2622K06P120Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622K06P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P120]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P120 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P120_replay] at h
  simpa only [momentPanelPhase_owner2622K06P120] using h

theorem momentScalarAmp2622K06P120_radius_le :
    (momentScalarAmp2622K06P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P120Expected]

def momentScalarGrow2622K06P120Input : RatPair2542 := (momentPanelGrowth2622K06P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P120Expected : RatState2542 :=
  ((((1395752978008456212286044201814769231553506700381067545817268730514440238674014366778439013907307 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3538653297432863145428338466558815938055995963741 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P120_replay :
    compactExp2620 momentScalarGrow2622K06P120Input 20 = momentScalarGrow2622K06P120Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P120_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P120] using h

theorem momentScalarGrow2622K06P120_radius_le :
    (momentScalarGrow2622K06P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P120Expected]

end ConnesWeilRH.Dev
