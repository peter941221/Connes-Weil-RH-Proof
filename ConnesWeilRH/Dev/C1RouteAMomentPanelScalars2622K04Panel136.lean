import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P136 : ℚ := ((-303131711263522530778460397872343257962843512639002139 : ℚ) / 8949128482804909646211664685642224404147097881804800)

def momentPanelGrowth2622K04P136 : ℚ := ((1615084462452961884506064272485206919341518576137316629 : ℚ) / 2887782655174593052634530025078670012982807132687564800)

theorem momentPanelPhase_owner2622K04P136 :
    (momentPanelPhase2622K04P136 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (93 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P136 :
    (momentPanelGrowth2622K04P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P136Input : RatPair2542 := (momentPanelPhase2622K04P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P136Expected : RatState2542 :=
  ((((2078808137589245359877887079713759118966060416812424921595992039065866468336806205 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5270575024881804806989031119570573 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P136_replay :
    compactExp2620 momentScalarAmp2622K04P136Input 20 = momentScalarAmp2622K04P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K04P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P136_replay] at h
  simpa only [momentPanelPhase_owner2622K04P136] using h

theorem momentScalarAmp2622K04P136_radius_le :
    (momentScalarAmp2622K04P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P136Expected]

def momentScalarGrow2622K04P136Input : RatPair2542 := (momentPanelGrowth2622K04P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P136Expected : RatState2542 :=
  ((((3736729316280210073711535122087953501800892421845486577215661739898558024261955765527506860256537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4736864634157848628605671157850854010474599555995 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P136_replay :
    compactExp2620 momentScalarGrow2622K04P136Input 20 = momentScalarGrow2622K04P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P136] using h

theorem momentScalarGrow2622K04P136_radius_le :
    (momentScalarGrow2622K04P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P136Expected]

end ConnesWeilRH.Dev
