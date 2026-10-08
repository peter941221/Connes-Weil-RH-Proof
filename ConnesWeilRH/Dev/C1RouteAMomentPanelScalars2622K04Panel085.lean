import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P085 : ℚ := ((-347395341280516857634682806969474350935850224099573817 : ℚ) / 11394860129025842498393143522890879269852572496691200)

def momentPanelGrowth2622K04P085 : ℚ := ((945611459159388395220678487903514882286994333732309 : ℚ) / 7573975330882717300812006154077635840242321509580800)

theorem momentPanelPhase_owner2622K04P085 :
    (momentPanelPhase2622K04P085 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P085, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P085 :
    (momentPanelGrowth2622K04P085 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P085, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P085Input : RatPair2542 := (momentPanelPhase2622K04P085 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P085Expected : RatState2542 :=
  ((((122815611645505825866052403912634182574448725097075510679099463797328449438081679413 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((77845905223702922711205816945949931 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P085_replay :
    compactExp2620 momentScalarAmp2622K04P085Input 20 = momentScalarAmp2622K04P085Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P085_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 200) 0) -
      (momentScalarAmp2622K04P085Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P085]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P085 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P085 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P085Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P085_replay] at h
  simpa only [momentPanelPhase_owner2622K04P085] using h

theorem momentScalarAmp2622K04P085_radius_le :
    (momentScalarAmp2622K04P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P085Expected]

def momentScalarGrow2622K04P085Input : RatPair2542 := (momentPanelGrowth2622K04P085 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P085Expected : RatState2542 :=
  ((((2420027578395817717670189279476903075413002753545549533984897063804428021817460255735548636914265 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((766937261764179714804766736627660680222865507203 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P085_replay :
    compactExp2620 momentScalarGrow2622K04P085Input 20 = momentScalarGrow2622K04P085Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P085_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P085Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P085]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P085 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P085 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P085Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P085_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P085] using h

theorem momentScalarGrow2622K04P085_radius_le :
    (momentScalarGrow2622K04P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P085Expected]

end ConnesWeilRH.Dev
