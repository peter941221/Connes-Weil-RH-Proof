import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P125 : ℚ := ((-19172637 : ℚ) / 582650)

def momentPanelGrowth2622K06P125 : ℚ := ((2405311 : ℚ) / 7398400)

theorem momentPanelPhase_owner2622K06P125 :
    (momentPanelPhase2622K06P125 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (71 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P125 :
    (momentPanelGrowth2622K06P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P125Input : RatPair2542 := (momentPanelPhase2622K06P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P125Expected : RatState2542 :=
  ((((683308983421261415398317283465573586168363816936765855566326768060906502920227353 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1732448452291868245995995580856701 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P125_replay :
    compactExp2620 momentScalarAmp2622K06P125Input 20 = momentScalarAmp2622K06P125Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622K06P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P125]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P125 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P125_replay] at h
  simpa only [momentPanelPhase_owner2622K06P125] using h

theorem momentScalarAmp2622K06P125_radius_le :
    (momentScalarAmp2622K06P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P125Expected]

def momentScalarGrow2622K06P125Input : RatPair2542 := (momentPanelGrowth2622K06P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P125Expected : RatState2542 :=
  ((((739150897219476427003313835320894290300169486763081575568811080197364162093925400034658232578783 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3747939152024536417793098372000783095197208607767 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P125_replay :
    compactExp2620 momentScalarGrow2622K06P125Input 20 = momentScalarGrow2622K06P125Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P125_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P125] using h

theorem momentScalarGrow2622K06P125_radius_le :
    (momentScalarGrow2622K06P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P125Expected]

end ConnesWeilRH.Dev
