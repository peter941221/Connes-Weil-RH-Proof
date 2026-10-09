import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P052 : ℚ := ((-801 : ℚ) / 22)

def momentPanelGrowth2622K06P052 : ℚ := ((13400107 : ℚ) / 38127675)

theorem momentPanelPhase_owner2622K06P052 :
    (momentPanelPhase2622K06P052 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 8) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P052, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P052 :
    (momentPanelGrowth2622K06P052 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P052, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P052Input : RatPair2542 := (momentPanelPhase2622K06P052 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P052Expected : RatState2542 :=
  ((((329102619846103373596537993497415644163627291175765534002198249945649093826328985 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((104300405499669211597792975044031 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P052_replay :
    compactExp2620 momentScalarAmp2622K06P052Input 20 = momentScalarAmp2622K06P052Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P052_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 8) 0) -
      (momentScalarAmp2622K06P052Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P052]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P052 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P052 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P052Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P052_replay] at h
  simpa only [momentPanelPhase_owner2622K06P052] using h

theorem momentScalarAmp2622K06P052_radius_le :
    (momentScalarAmp2622K06P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P052Expected]

def momentScalarGrow2622K06P052Input : RatPair2542 := (momentPanelGrowth2622K06P052 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P052Expected : RatState2542 :=
  ((((3035518981632391011272638216066632797500153938118730473159805743391381785252764152487978649827021 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3847976169335511513259596184144336735482316683081 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P052_replay :
    compactExp2620 momentScalarGrow2622K06P052Input 20 = momentScalarGrow2622K06P052Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P052_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P052Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P052]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P052 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P052 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P052Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P052_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P052] using h

theorem momentScalarGrow2622K06P052_radius_le :
    (momentScalarGrow2622K06P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P052Expected]

end ConnesWeilRH.Dev
