import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P025 : ℚ := ((-63013311 : ℚ) / 1167950)

def momentPanelGrowth2622K06P025 : ℚ := ((537787 : ℚ) / 444675)

theorem momentPanelPhase_owner2622K06P025 :
    (momentPanelPhase2622K06P025 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-129 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P025, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P025 :
    (momentPanelGrowth2622K06P025 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P025, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P025Input : RatPair2542 := (momentPanelPhase2622K06P025 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P025Expected : RatState2542 :=
  ((((989522655530437878312062233324426319290057644854889129845754648221139587 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((12453319883632465339523245 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P025_replay :
    compactExp2620 momentScalarAmp2622K06P025Input 20 = momentScalarAmp2622K06P025Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P025_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-129 / 200) 0) -
      (momentScalarAmp2622K06P025Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P025]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P025 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P025 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P025Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P025_replay] at h
  simpa only [momentPanelPhase_owner2622K06P025] using h

theorem momentScalarAmp2622K06P025_radius_le :
    (momentScalarAmp2622K06P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P025Expected]

def momentScalarGrow2622K06P025Input : RatPair2542 := (momentPanelGrowth2622K06P025 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P025Expected : RatState2542 :=
  ((((3579327910817405255945674386504691884741877711645630265553122332091054283909707930129879707869241 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((9074663882695131903263554751768036715870687797451 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P025_replay :
    compactExp2620 momentScalarGrow2622K06P025Input 20 = momentScalarGrow2622K06P025Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P025_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P025Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P025]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P025 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P025 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P025Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P025_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P025] using h

theorem momentScalarGrow2622K06P025_radius_le :
    (momentScalarGrow2622K06P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P025Expected]

end ConnesWeilRH.Dev
