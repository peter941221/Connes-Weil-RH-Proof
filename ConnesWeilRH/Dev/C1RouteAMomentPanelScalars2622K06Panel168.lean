import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P168 : ℚ := ((-19196631 : ℚ) / 255850)

def momentPanelGrowth2622K06P168 : ℚ := ((399710027 : ℚ) / 117750675)

theorem momentPanelPhase_owner2622K06P168 :
    (momentPanelPhase2622K06P168 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P168 :
    (momentPanelGrowth2622K06P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P168Input : RatPair2542 := (momentPanelPhase2622K06P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P168Expected : RatState2542 :=
  ((((2773989495165127874006807744931119365252857059039674944639333991 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851646262660749741169 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P168_replay :
    compactExp2620 momentScalarAmp2622K06P168Input 20 = momentScalarAmp2622K06P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K06P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P168_replay] at h
  simpa only [momentPanelPhase_owner2622K06P168] using h

theorem momentScalarAmp2622K06P168_radius_le :
    (momentScalarAmp2622K06P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P168Expected]

def momentScalarGrow2622K06P168Input : RatPair2542 := (momentPanelGrowth2622K06P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P168Expected : RatState2542 :=
  ((((7956847160537114769024231747187576511168261228633004916067475074786558065356042788025211211521717 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((10086469426090778469955140852539815197792687991119 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P168_replay :
    compactExp2620 momentScalarGrow2622K06P168Input 20 = momentScalarGrow2622K06P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P168] using h

theorem momentScalarGrow2622K06P168_radius_le :
    (momentScalarGrow2622K06P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P168Expected]

end ConnesWeilRH.Dev
