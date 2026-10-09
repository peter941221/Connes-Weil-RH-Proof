import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P049 : ℚ := ((-85814821566279744878805343030547430842469884340080607 : ℚ) / 2386286779819729623135401226621083393275133217996800)

def momentPanelGrowth2622K01P049 : ℚ := ((294118482405268156549526497926900474141171086099216251 : ℚ) / 823114689243417523367568048928125516493056394867507200)

theorem momentPanelPhase_owner2622K01P049 :
    (momentPanelPhase2622K01P049 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P049 :
    (momentPanelGrowth2622K01P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P049Input : RatPair2542 := (momentPanelPhase2622K01P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P049Expected : RatState2542 :=
  ((((64351749872854363552304407729719282644945126392570849854097780306453499703501073 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((652626659142880347115119850577871 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P049_replay :
    compactExp2620 momentScalarAmp2622K01P049Input 20 = momentScalarAmp2622K01P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K01P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P049_replay] at h
  simpa only [momentPanelPhase_owner2622K01P049] using h

theorem momentScalarAmp2622K01P049_radius_le :
    (momentScalarAmp2622K01P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P049Expected]

def momentScalarGrow2622K01P049Input : RatPair2542 := (momentPanelGrowth2622K01P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P049Expected : RatState2542 :=
  ((((381673833866305720887523741736152212314976947926669592738343426164585984856279690180144215116665 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((483828899717365208433123684418245986282882790047 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P049_replay :
    compactExp2620 momentScalarGrow2622K01P049Input 20 = momentScalarGrow2622K01P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P049] using h

theorem momentScalarGrow2622K01P049_radius_le :
    (momentScalarGrow2622K01P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P049Expected]

end ConnesWeilRH.Dev
