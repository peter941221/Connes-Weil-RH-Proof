import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P056 : ℚ := ((-20793079 : ℚ) / 591850)

def momentPanelGrowth2622K06P056 : ℚ := ((12254507 : ℚ) / 40737675)

theorem momentPanelPhase_owner2622K06P056 :
    (momentPanelPhase2622K06P056 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P056 :
    (momentPanelGrowth2622K06P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P056Input : RatPair2542 := (momentPanelPhase2622K06P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P056Expected : RatState2542 :=
  ((((1179816848200609001341958433026692947404128994506032442626183310966192891937682971 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((186955706086445718863142061056543 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P056_replay :
    compactExp2620 momentScalarAmp2622K06P056Input 20 = momentScalarAmp2622K06P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K06P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P056_replay] at h
  simpa only [momentPanelPhase_owner2622K06P056] using h

theorem momentScalarAmp2622K06P056_radius_le :
    (momentScalarAmp2622K06P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P056Expected]

def momentScalarGrow2622K06P056Input : RatPair2542 := (momentPanelGrowth2622K06P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P056Expected : RatState2542 :=
  ((((360703997309364454891573755853663295106580364625881432645507763870847035276661645807240211631475 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((914493015038431815522589237704919807507832806703 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P056_replay :
    compactExp2620 momentScalarGrow2622K06P056Input 20 = momentScalarGrow2622K06P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P056] using h

theorem momentScalarGrow2622K06P056_radius_le :
    (momentScalarGrow2622K06P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P056Expected]

end ConnesWeilRH.Dev
