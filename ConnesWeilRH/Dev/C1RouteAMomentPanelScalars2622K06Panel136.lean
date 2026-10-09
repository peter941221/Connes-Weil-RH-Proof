import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P136 : ℚ := ((-57084357 : ℚ) / 1567550)

def momentPanelGrowth2622K06P136 : ℚ := ((255233227 : ℚ) / 505830675)

theorem momentPanelPhase_owner2622K06P136 :
    (momentPanelPhase2622K06P136 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (93 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P136 :
    (momentPanelGrowth2622K06P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P136Input : RatPair2542 := (momentPanelPhase2622K06P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P136Expected : RatState2542 :=
  ((((326741552230783181648598891958567240565339904393795769206561505113381160780711091 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((414208512136830743743519135254365 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P136_replay :
    compactExp2620 momentScalarAmp2622K06P136Input 20 = momentScalarAmp2622K06P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K06P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P136_replay] at h
  simpa only [momentPanelPhase_owner2622K06P136] using h

theorem momentScalarAmp2622K06P136_radius_le :
    (momentScalarAmp2622K06P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P136Expected]

def momentScalarGrow2622K06P136Input : RatPair2542 := (momentPanelGrowth2622K06P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P136Expected : RatState2542 :=
  ((((3537821684745593305926867456390481548518101524768846499947892471935253464184050923817580601423529 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4484719624088211849721237544143240314238909716745 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P136_replay :
    compactExp2620 momentScalarGrow2622K06P136Input 20 = momentScalarGrow2622K06P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P136] using h

theorem momentScalarGrow2622K06P136_radius_le :
    (momentScalarGrow2622K06P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P136Expected]

end ConnesWeilRH.Dev
