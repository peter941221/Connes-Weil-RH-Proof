import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P059 : ℚ := ((-73274553833754329795641251043708545371135486573935025 : ℚ) / 2209242412530326123729645085254751319587399030276096)

def momentPanelGrowth2622K03P059 : ℚ := ((573696286697150307778706834247748275677641098442081475 : ℚ) / 2487704785774996052633667625150339932050039527075479552)

theorem momentPanelPhase_owner2622K03P059 :
    (momentPanelPhase2622K03P059 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-61 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P059, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P059 :
    (momentPanelGrowth2622K03P059 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P059, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P059Input : RatPair2542 := (momentPanelPhase2622K03P059 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P059Expected : RatState2542 :=
  ((((1052309485167123791220630970350178951325536920642687165088859451547015976389932283 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2668005891372274263850372946216813 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P059_replay :
    compactExp2620 momentScalarAmp2622K03P059Input 20 = momentScalarAmp2622K03P059Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P059_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-61 / 200) 0) -
      (momentScalarAmp2622K03P059Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P059]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P059 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P059 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P059Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P059_replay] at h
  simpa only [momentPanelPhase_owner2622K03P059] using h

theorem momentScalarAmp2622K03P059_radius_le :
    (momentScalarAmp2622K03P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P059Expected]

def momentScalarGrow2622K03P059Input : RatPair2542 := (momentPanelGrowth2622K03P059 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P059Expected : RatState2542 :=
  ((((1345000465071800185131025258253746625107289658265212910589492552464834747114928085240473735378807 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3409980543755982412752318856708009830044680800779 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P059_replay :
    compactExp2620 momentScalarGrow2622K03P059Input 20 = momentScalarGrow2622K03P059Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P059_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P059Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P059]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P059 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P059 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P059Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P059_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P059] using h

theorem momentScalarGrow2622K03P059_radius_le :
    (momentScalarGrow2622K03P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P059Expected]

end ConnesWeilRH.Dev
