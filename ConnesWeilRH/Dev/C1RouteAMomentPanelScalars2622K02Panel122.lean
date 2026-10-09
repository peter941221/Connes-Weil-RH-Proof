import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P122 : ℚ := ((-877254274660400133892765879292750775513273956372521 : ℚ) / 27231885976829714530592096297096367202182805585920)

def momentPanelGrowth2622K02P122 : ℚ := ((3289302083137653834643954429817033363454948531529837359 : ℚ) / 11333191753444172654448365208551502428949260418836070400)

theorem momentPanelPhase_owner2622K02P122 :
    (momentPanelPhase2622K02P122 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P122 :
    (momentPanelGrowth2622K02P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P122Input : RatPair2542 := (momentPanelPhase2622K02P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P122Expected : RatState2542 :=
  ((((10917060257676253540158998836341683451813579601286536191828882306678203796129650663 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((27678886313661542256541653368404793 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P122_replay :
    compactExp2620 momentScalarAmp2622K02P122Input 20 = momentScalarAmp2622K02P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K02P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P122_replay] at h
  simpa only [momentPanelPhase_owner2622K02P122] using h

theorem momentScalarAmp2622K02P122_radius_le :
    (momentScalarAmp2622K02P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P122Expected]

def momentScalarGrow2622K02P122Input : RatPair2542 := (momentPanelGrowth2622K02P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P122Expected : RatState2542 :=
  ((((1427633007974693314169191471096612734818262323438871208303421090035704527626286654499713669318087 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((452434834636382830866188972520657418238191839615 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P122_replay :
    compactExp2620 momentScalarGrow2622K02P122Input 20 = momentScalarGrow2622K02P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P122] using h

theorem momentScalarGrow2622K02P122_radius_le :
    (momentScalarGrow2622K02P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P122Expected]

end ConnesWeilRH.Dev
