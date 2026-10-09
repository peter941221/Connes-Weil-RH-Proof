import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P123 : ℚ := ((-19206921 : ℚ) / 591850)

def momentPanelGrowth2622K06P123 : ℚ := ((12254507 : ℚ) / 40737675)

theorem momentPanelPhase_owner2622K06P123 :
    (momentPanelPhase2622K06P123 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (67 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P123 :
    (momentPanelGrowth2622K06P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P123Input : RatPair2542 := (momentPanelPhase2622K06P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P123Expected : RatState2542 :=
  ((((17207738803057905679240914428671124954035576655170055579682872090611194837665643287 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5453518884345865627565410703066081 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P123_replay :
    compactExp2620 momentScalarAmp2622K06P123Input 20 = momentScalarAmp2622K06P123Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622K06P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P123]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P123 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P123_replay] at h
  simpa only [momentPanelPhase_owner2622K06P123] using h

theorem momentScalarAmp2622K06P123_radius_le :
    (momentScalarAmp2622K06P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P123Expected]

def momentScalarGrow2622K06P123Input : RatPair2542 := (momentPanelGrowth2622K06P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P123Expected : RatState2542 :=
  ((((360703997309364454891573755853663295106580364625881432645507763870847035276661645807240211631475 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((914493015038431815522589237704919807507832806703 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P123_replay :
    compactExp2620 momentScalarGrow2622K06P123Input 20 = momentScalarGrow2622K06P123Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P123_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P123] using h

theorem momentScalarGrow2622K06P123_radius_le :
    (momentScalarGrow2622K06P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P123Expected]

end ConnesWeilRH.Dev
