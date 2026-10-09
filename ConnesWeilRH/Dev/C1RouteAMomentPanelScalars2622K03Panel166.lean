import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P166 : ℚ := ((-218538838167861415655631400428688977781981062689946225 : ℚ) / 3030971708119626289489666882449481447388947102564352)

def momentPanelGrowth2622K03P166 : ℚ := ((1408189148212189321943309664438890767001419243444383475 : ℚ) / 504615136605253846466860730910106246924199498499489792)

theorem momentPanelPhase_owner2622K03P166 :
    (momentPanelPhase2622K03P166 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (153 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P166 :
    (momentPanelGrowth2622K03P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P166Input : RatPair2542 := (momentPanelPhase2622K03P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P166Expected : RatState2542 :=
  ((((810827727883847475986016186306337827415616085567410532230415675 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((604462942700656769252347 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P166_replay :
    compactExp2620 momentScalarAmp2622K03P166Input 20 = momentScalarAmp2622K03P166Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622K03P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P166]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P166 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P166_replay] at h
  simpa only [momentPanelPhase_owner2622K03P166] using h

theorem momentScalarAmp2622K03P166_radius_le :
    (momentScalarAmp2622K03P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P166Expected]

def momentScalarGrow2622K03P166Input : RatPair2542 := (momentPanelGrowth2622K03P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P166Expected : RatState2542 :=
  ((((4349702362966473851460471398057310689793618893595744677598762712695829413826170351073337094073089 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((689236017107873253246516371883753481303172801779 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K03P166_replay :
    compactExp2620 momentScalarGrow2622K03P166Input 20 = momentScalarGrow2622K03P166Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P166_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P166] using h

theorem momentScalarGrow2622K03P166_radius_le :
    (momentScalarGrow2622K03P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P166Expected]

end ConnesWeilRH.Dev
