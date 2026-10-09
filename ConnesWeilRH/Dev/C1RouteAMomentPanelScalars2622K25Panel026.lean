import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P026 : ℚ := ((-827168615033325772808168394640929623891 : ℚ) / 16138713321625634156334827848282931200)

def momentPanelGrowth2622K25P026 : ℚ := ((51418903911122094917207214744933002803 : ℚ) / 46027886234046918276584694705920409600)

theorem momentPanelPhase_owner2622K25P026 :
    (momentPanelPhase2622K25P026 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-127 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P026 :
    (momentPanelGrowth2622K25P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P026Input : RatPair2542 := (momentPanelPhase2622K25P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P026Expected : RatState2542 :=
  ((((14699878146064481458477800948102330996975942393261278140341102393819287211 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((151499613318641840186084947 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K25P026_replay :
    compactExp2620 momentScalarAmp2622K25P026Input 20 = momentScalarAmp2622K25P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K25P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P026_replay] at h
  simpa only [momentPanelPhase_owner2622K25P026] using h

theorem momentScalarAmp2622K25P026_radius_le :
    (momentScalarAmp2622K25P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P026Expected]

def momentScalarGrow2622K25P026Input : RatPair2542 := (momentPanelGrowth2622K25P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P026Expected : RatState2542 :=
  ((((3263847466147438529496068662583120271770936461268829072955156058846325455421353747134945036245419 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8274827583244050598257714814911676980882681246901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K25P026_replay :
    compactExp2620 momentScalarGrow2622K25P026Input 20 = momentScalarGrow2622K25P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P026] using h

theorem momentScalarGrow2622K25P026_radius_le :
    (momentScalarGrow2622K25P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P026Expected]

end ConnesWeilRH.Dev
