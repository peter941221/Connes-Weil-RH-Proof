import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P123 : ℚ := ((-103460585711437866180450305261131829147819488533985367 : ℚ) / 3378866187712089422417386204074734785872514357657600)

def momentPanelGrowth2622K04P123 : ℚ := ((82682390009721270614720667326889213673310295830996189 : ℚ) / 232571010599821056790364439521973847120164030303436800)

theorem momentPanelPhase_owner2622K04P123 :
    (momentPanelPhase2622K04P123 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (67 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P123 :
    (momentPanelGrowth2622K04P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P123Input : RatPair2542 := (momentPanelPhase2622K04P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P123Expected : RatState2542 :=
  ((((53766250300202383354550201650493407819737990936870516840843149124226404389912120745 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((68158809771508312031574201756178955 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P123_replay :
    compactExp2620 momentScalarAmp2622K04P123Input 20 = momentScalarAmp2622K04P123Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622K04P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P123]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P123 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P123_replay] at h
  simpa only [momentPanelPhase_owner2622K04P123] using h

theorem momentScalarAmp2622K04P123_radius_le :
    (momentScalarAmp2622K04P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P123Expected]

def momentScalarGrow2622K04P123Input : RatPair2542 := (momentPanelGrowth2622K04P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P123Expected : RatState2542 :=
  ((((380983927781618828298217172275327031646283273235184580371663434859938194019294579907443603452579 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3863634727890605537274083864594804338165578278855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P123_replay :
    compactExp2620 momentScalarGrow2622K04P123Input 20 = momentScalarGrow2622K04P123Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P123_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P123] using h

theorem momentScalarGrow2622K04P123_radius_le :
    (momentScalarGrow2622K04P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P123Expected]

end ConnesWeilRH.Dev
