import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P028 : ℚ := ((-63059133 : ℚ) / 1243550)

def momentPanelGrowth2622K06P028 : ℚ := ((20164507 : ℚ) / 19737675)

theorem momentPanelPhase_owner2622K06P028 :
    (momentPanelPhase2622K06P028 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P028 :
    (momentPanelGrowth2622K06P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P028Input : RatPair2542 := (momentPanelPhase2622K06P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P028Expected : RatState2542 :=
  ((((202756636720780397741832805847967230749862618199891625854251300145534551723 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((259454853845655193176205665 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P028_replay :
    compactExp2620 momentScalarAmp2622K06P028Input 20 = momentScalarAmp2622K06P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K06P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P028_replay] at h
  simpa only [momentPanelPhase_owner2622K06P028] using h

theorem momentScalarAmp2622K06P028_radius_le :
    (momentScalarAmp2622K06P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P028Expected]

def momentScalarGrow2622K06P028Input : RatPair2542 := (momentPanelGrowth2622K06P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P028Expected : RatState2542 :=
  ((((5933143025938815724050794173625610981639151557432023636545546329752909202021045222304494866087681 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1880286247558257287585435466155795346719617286433 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P028_replay :
    compactExp2620 momentScalarGrow2622K06P028Input 20 = momentScalarGrow2622K06P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P028] using h

theorem momentScalarGrow2622K06P028_radius_le :
    (momentScalarGrow2622K06P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P028Expected]

end ConnesWeilRH.Dev
