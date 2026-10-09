import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P160 : ℚ := ((-57163221 : ℚ) / 1005950)

def momentPanelGrowth2622K06P160 : ℚ := ((363197227 : ℚ) / 204930675)

theorem momentPanelPhase_owner2622K06P160 :
    (momentPanelPhase2622K06P160 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P160 :
    (momentPanelGrowth2622K06P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P160Input : RatPair2542 := (momentPanelPhase2622K06P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P160Expected : RatState2542 :=
  ((((447472362723405499410347115180636349465402058552039048566594735302742521 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((746280247354850403564803 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P160_replay :
    compactExp2620 momentScalarAmp2622K06P160Input 20 = momentScalarAmp2622K06P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K06P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P160_replay] at h
  simpa only [momentPanelPhase_owner2622K06P160] using h

theorem momentScalarAmp2622K06P160_radius_le :
    (momentScalarAmp2622K06P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P160Expected]

def momentScalarGrow2622K06P160Input : RatPair2542 := (momentPanelGrowth2622K06P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P160Expected : RatState2542 :=
  ((((6284427821167183168397083189014767484880261846045552520331204209602515756225818686309686640887413 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3983222617386315109996058043831810823410484117821 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P160_replay :
    compactExp2620 momentScalarGrow2622K06P160Input 20 = momentScalarGrow2622K06P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P160] using h

theorem momentScalarGrow2622K06P160_radius_le :
    (momentScalarGrow2622K06P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P160Expected]

end ConnesWeilRH.Dev
