import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P028 : ℚ := ((-220052456677531107393221356619597028740620612474635525 : ℚ) / 4543625902757110809830480684310834372732837284544512)

def momentPanelGrowth2622K03P028 : ℚ := ((71004973803570152210417072102825593382300006190156475 : ℚ) / 72116610824013073140139787576458403624968520887959552)

theorem momentPanelPhase_owner2622K03P028 :
    (momentPanelPhase2622K03P028 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P028 :
    (momentPanelGrowth2622K03P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P028Input : RatPair2542 := (momentPanelPhase2622K03P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P028Expected : RatState2542 :=
  ((((123638010212472195837543146134782460842557494869673527883602881550702939099 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((627552610788534038090146157 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P028_replay :
    compactExp2620 momentScalarAmp2622K03P028Input 20 = momentScalarAmp2622K03P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K03P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P028_replay] at h
  simpa only [momentPanelPhase_owner2622K03P028] using h

theorem momentScalarAmp2622K03P028_radius_le :
    (momentScalarAmp2622K03P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P028Expected]

def momentScalarGrow2622K03P028Input : RatPair2542 := (momentPanelGrowth2622K03P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P028Expected : RatState2542 :=
  ((((714675183839807237859602080637428143628977281088463225518869693251015610971421183950536228348155 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((7247660600734224065569056040330593890296839245427 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P028_replay :
    compactExp2620 momentScalarGrow2622K03P028Input 20 = momentScalarGrow2622K03P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P028] using h

theorem momentScalarGrow2622K03P028_radius_le :
    (momentScalarGrow2622K03P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P028Expected]

end ConnesWeilRH.Dev
