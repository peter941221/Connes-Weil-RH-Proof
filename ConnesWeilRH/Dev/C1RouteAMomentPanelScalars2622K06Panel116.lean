import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P116 : ℚ := ((-19342959 : ℚ) / 619850)

def momentPanelGrowth2622K06P116 : ℚ := ((490951441 : ℚ) / 2148786025)

theorem momentPanelPhase_owner2622K06P116 :
    (momentPanelPhase2622K06P116 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P116 :
    (momentPanelGrowth2622K06P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P116Input : RatPair2542 := (momentPanelPhase2622K06P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P116Expected : RatState2542 :=
  ((((59849583413925105056967133720204231479622271197296742655609482062758357688349113525 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((37935309117253946776808553517100625 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P116_replay :
    compactExp2620 momentScalarAmp2622K06P116Input 20 = momentScalarAmp2622K06P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K06P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P116_replay] at h
  simpa only [momentPanelPhase_owner2622K06P116] using h

theorem momentScalarAmp2622K06P116_radius_le :
    (momentScalarAmp2622K06P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P116Expected]

def momentScalarGrow2622K06P116Input : RatPair2542 := (momentPanelGrowth2622K06P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P116Expected : RatState2542 :=
  ((((2684266126664250405405166770988438339998939161866458841441215578912536398410582565003963236889215 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((850677706301893765990544044907327424978826830543 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P116_replay :
    compactExp2620 momentScalarGrow2622K06P116Input 20 = momentScalarGrow2622K06P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P116] using h

theorem momentScalarGrow2622K06P116_radius_le :
    (momentScalarGrow2622K06P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P116Expected]

end ConnesWeilRH.Dev
