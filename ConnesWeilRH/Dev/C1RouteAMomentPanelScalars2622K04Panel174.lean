import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P174 : ℚ := ((-105470166738050091877258484110829758670674923477736781 : ℚ) / 1088419090457565005295048880302184991005482575462400)

def momentPanelGrowth2622K04P174 : ℚ := ((3937623801212553533537167600664947674300864950490389 : ℚ) / 586170627394337723150638047652907652512394038476800)

theorem momentPanelPhase_owner2622K04P174 :
    (momentPanelPhase2622K04P174 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P174 :
    (momentPanelGrowth2622K04P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P174Input : RatPair2542 := (momentPanelPhase2622K04P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P174Expected : RatState2542 :=
  ((((1760041429574420295683898441701197760739745850969612905 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629175824033 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P174_replay :
    compactExp2620 momentScalarAmp2622K04P174Input 20 = momentScalarAmp2622K04P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K04P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P174_replay] at h
  simpa only [momentPanelPhase_owner2622K04P174] using h

theorem momentScalarAmp2622K04P174_radius_le :
    (momentScalarAmp2622K04P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P174Expected]

def momentScalarGrow2622K04P174Input : RatPair2542 := (momentPanelGrowth2622K04P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P174Expected : RatState2542 :=
  ((((441497812753356647957090135012202222300922435929899105044612922226512277033556539521707600212451119 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1119322763882834542025266799119415707184083924903811 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P174_replay :
    compactExp2620 momentScalarGrow2622K04P174Input 20 = momentScalarGrow2622K04P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P174] using h

theorem momentScalarGrow2622K04P174_radius_le :
    (momentScalarGrow2622K04P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P174Expected]

end ConnesWeilRH.Dev
