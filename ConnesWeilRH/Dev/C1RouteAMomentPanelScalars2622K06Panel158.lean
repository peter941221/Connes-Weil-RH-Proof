import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P158 : ℚ := ((-19030451 : ℚ) / 353850)

def momentPanelGrowth2622K06P158 : ℚ := ((1062447121 : ℚ) / 686178025)

theorem momentPanelPhase_owner2622K06P158 :
    (momentPanelPhase2622K06P158 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (137 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P158 :
    (momentPanelGrowth2622K06P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P158Input : RatPair2542 := (momentPanelPhase2622K06P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P158Expected : RatState2542 :=
  ((((4695943883804651778510922813279045097820893575224411878201528148328141899 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1790511807102308842696853 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P158_replay :
    compactExp2620 momentScalarAmp2622K06P158Input 20 = momentScalarAmp2622K06P158Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622K06P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P158]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P158 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P158_replay] at h
  simpa only [momentPanelPhase_owner2622K06P158] using h

theorem momentScalarAmp2622K06P158_radius_le :
    (momentScalarAmp2622K06P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P158Expected]

def momentScalarGrow2622K06P158Input : RatPair2542 := (momentPanelGrowth2622K06P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P158Expected : RatState2542 :=
  ((((627943584283688574525071966515372198154376884959850936622692322471129073829842805325641987820503 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((12736190177819420807895292687702270083490685718785 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P158_replay :
    compactExp2620 momentScalarGrow2622K06P158Input 20 = momentScalarGrow2622K06P158Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P158_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P158] using h

theorem momentScalarGrow2622K06P158_radius_le :
    (momentScalarGrow2622K06P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P158Expected]

end ConnesWeilRH.Dev
