import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P099 : ℚ := ((-110786672413370029582155493503551679130550263701332231 : ℚ) / 3771644752744769581684626502867235847405046228582400)

def momentPanelGrowth2622K04P099 : ℚ := ((72701618507151450022077196917965405822640915727709 : ℚ) / 466281821207037093141742026219150061056243322060800)

theorem momentPanelPhase_owner2622K04P099 :
    (momentPanelPhase2622K04P099 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (19 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P099, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P099 :
    (momentPanelGrowth2622K04P099 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P099, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P099Input : RatPair2542 := (momentPanelPhase2622K04P099 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P099Expected : RatState2542 :=
  ((((46744349056860352028188238596595119056822461991707706686975162156539494753718882775 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((474057296611607438768231435180834933 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P099_replay :
    compactExp2620 momentScalarAmp2622K04P099Input 20 = momentScalarAmp2622K04P099Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P099_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (19 / 200) 0) -
      (momentScalarAmp2622K04P099Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P099]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P099 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P099 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P099Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P099_replay] at h
  simpa only [momentPanelPhase_owner2622K04P099] using h

theorem momentScalarAmp2622K04P099_radius_le :
    (momentScalarAmp2622K04P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P099Expected]

def momentScalarGrow2622K04P099Input : RatPair2542 := (momentPanelGrowth2622K04P099 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P099Expected : RatState2542 :=
  ((((1248196156439618914130985230212483901802749575107423688123277697641237880454826554470401740587787 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3164552743274038852014757458104615188553384649523 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P099_replay :
    compactExp2620 momentScalarGrow2622K04P099Input 20 = momentScalarGrow2622K04P099Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P099_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P099Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P099]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P099 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P099 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P099Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P099_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P099] using h

theorem momentScalarGrow2622K04P099_radius_le :
    (momentScalarGrow2622K04P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P099Expected]

end ConnesWeilRH.Dev
