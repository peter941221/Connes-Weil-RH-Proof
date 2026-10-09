import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P013 : ℚ := ((-219911653031409459805474049386195928114798700202853775 : ℚ) / 3030971708119626289489666882449481447388947102564352)

def momentPanelGrowth2622K03P013 : ℚ := ((1408189148212189321943309664438890767001419243444383475 : ℚ) / 504615136605253846466860730910106246924199498499489792)

theorem momentPanelPhase_owner2622K03P013 :
    (momentPanelPhase2622K03P013 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P013 :
    (momentPanelGrowth2622K03P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P013Input : RatPair2542 := (momentPanelPhase2622K03P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P013Expected : RatState2542 :=
  ((((32991648594692384981567657176411213729332579250051774695219656869 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((604462930719703326743675 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P013_replay :
    compactExp2620 momentScalarAmp2622K03P013Input 20 = momentScalarAmp2622K03P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K03P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P013_replay] at h
  simpa only [momentPanelPhase_owner2622K03P013] using h

theorem momentScalarAmp2622K03P013_radius_le :
    (momentScalarAmp2622K03P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P013Expected]

def momentScalarGrow2622K03P013Input : RatPair2542 := (momentPanelGrowth2622K03P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P013Expected : RatState2542 :=
  ((((4349702362966473851460471398057310689793618893595744677598762712695829413826170351073337094073089 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((689236017107873253246516371883753481303172801779 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K03P013_replay :
    compactExp2620 momentScalarGrow2622K03P013Input 20 = momentScalarGrow2622K03P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P013] using h

theorem momentScalarGrow2622K03P013_radius_le :
    (momentScalarGrow2622K03P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P013Expected]

end ConnesWeilRH.Dev
