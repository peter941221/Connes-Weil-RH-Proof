import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P174 : ℚ := ((-72900832385740376766896036033306096518742234488395275 : ℚ) / 696588217892841603388831283393398394243508848295936)

def momentPanelGrowth2622K03P174 : ℚ := ((2485663345146815283280919188265754572124252793820675 : ℚ) / 375149201532376142816408350497860897607932184625152)

theorem momentPanelPhase_owner2622K03P174 :
    (momentPanelPhase2622K03P174 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P174 :
    (momentPanelGrowth2622K03P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P174Input : RatPair2542 := (momentPanelPhase2622K03P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P174Expected : RatState2542 :=
  ((((94579803971106995086226958361480693786420190705845 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417851639229258349413403 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P174_replay :
    compactExp2620 momentScalarAmp2622K03P174Input 20 = momentScalarAmp2622K03P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K03P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P174_replay] at h
  simpa only [momentPanelPhase_owner2622K03P174] using h

theorem momentScalarAmp2622K03P174_radius_le :
    (momentScalarAmp2622K03P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P174Expected]

def momentScalarGrow2622K03P174Input : RatPair2542 := (momentPanelGrowth2622K03P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P174Expected : RatState2542 :=
  ((((201398732203336819833760972215794078190176130670601260692679872300013741470933546565724254043418455 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((510603221087776805605663860873848655229726569509031 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P174_replay :
    compactExp2620 momentScalarGrow2622K03P174Input 20 = momentScalarGrow2622K03P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P174] using h

theorem momentScalarGrow2622K03P174_radius_le :
    (momentScalarGrow2622K03P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P174Expected]

end ConnesWeilRH.Dev
