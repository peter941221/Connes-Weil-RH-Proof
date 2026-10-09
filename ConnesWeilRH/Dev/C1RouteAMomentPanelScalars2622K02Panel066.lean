import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P066 : ℚ := ((-117634614655978292485639345102330260613801698647251061 : ℚ) / 3595807837003395324338245671431058046602691844505600)

def momentPanelGrowth2622K02P066 : ℚ := ((10052631395698678290576404707262928223421187845776359 : ℚ) / 49514219680124430789662162680738830220903884154470400)

theorem momentPanelPhase_owner2622K02P066 :
    (momentPanelPhase2622K02P066 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P066 :
    (momentPanelGrowth2622K02P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P066Input : RatPair2542 := (momentPanelPhase2622K02P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P066Expected : RatState2542 :=
  ((((6620564650809192800638360789933740297297983593011034022381767880177769338578123053 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((16785649194289231858207556279006731 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P066_replay :
    compactExp2620 momentScalarAmp2622K02P066Input 20 = momentScalarAmp2622K02P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K02P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P066_replay] at h
  simpa only [momentPanelPhase_owner2622K02P066] using h

theorem momentScalarAmp2622K02P066_radius_le :
    (momentScalarAmp2622K02P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P066Expected]

def momentScalarGrow2622K02P066Input : RatPair2542 := (momentPanelGrowth2622K02P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P066Expected : RatState2542 :=
  ((((327100587072302642768005305475201620930577545675849474588007322102988346741311522559153111416057 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1658596701011547455800154624345498319896736620369 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P066_replay :
    compactExp2620 momentScalarGrow2622K02P066Input 20 = momentScalarGrow2622K02P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P066] using h

theorem momentScalarGrow2622K02P066_radius_le :
    (momentScalarGrow2622K02P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P066Expected]

end ConnesWeilRH.Dev
