import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P028 : ℚ := ((-2481938030602064637596923327993922365077 : ℚ) / 50444380925242069511399208673450393600)

def momentPanelGrowth2622K25P028 : ℚ := ((798343920157073282055530186750491383083 : ℚ) / 800655217947510968069966126053431705600)

theorem momentPanelPhase_owner2622K25P028 :
    (momentPanelPhase2622K25P028 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P028 :
    (momentPanelGrowth2622K25P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P028Input : RatPair2542 := (momentPanelPhase2622K25P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P028Expected : RatState2542 :=
  ((((457761014450418924094649077363571776035395249319230419188942321660236939231 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1163034358482007525677338263 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K25P028_replay :
    compactExp2620 momentScalarAmp2622K25P028Input 20 = momentScalarAmp2622K25P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K25P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P028_replay] at h
  simpa only [momentPanelPhase_owner2622K25P028] using h

theorem momentScalarAmp2622K25P028_radius_le :
    (momentScalarAmp2622K25P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P028Expected]

def momentScalarGrow2622K25P028Input : RatPair2542 := (momentPanelGrowth2622K25P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P028Expected : RatState2542 :=
  ((((723684722322909430644928757319798129181271468801017639234798024434089250633104581123006378317171 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3669514001093897807045485385813404648449967228481 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K25P028_replay :
    compactExp2620 momentScalarGrow2622K25P028Input 20 = momentScalarGrow2622K25P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P028] using h

theorem momentScalarGrow2622K25P028_radius_le :
    (momentScalarGrow2622K25P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P028Expected]

end ConnesWeilRH.Dev
