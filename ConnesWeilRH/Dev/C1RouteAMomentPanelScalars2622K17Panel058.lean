import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K17
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K17P058 : ℚ := ((-2469542618676738625658816374292180457657 : ℚ) / 73079550042917333704524341108644249600)

def momentPanelGrowth2622K17P058 : ℚ := ((27000754571342985777458058876759765683 : ℚ) / 106388337214514289458251714533104025600)

theorem momentPanelPhase_owner2622K17P058 :
    (momentPanelPhase2622K17P058 : ℝ) = momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (-63 / 200) 0 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K17P058 :
    (momentPanelGrowth2622K17P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K17P058Input : RatPair2542 := (momentPanelPhase2622K17P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K17P058Expected : RatState2542 :=
  ((((4504959591063368920203221765634660149439764227019323184037383889674195542998716791 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5710898774570417098512907903439859 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K17P058_replay :
    compactExp2620 momentScalarAmp2622K17P058Input 20 = momentScalarAmp2622K17P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K17P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K17P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K17P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K17P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K17P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K17P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K17P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K17P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K17P058_replay] at h
  simpa only [momentPanelPhase_owner2622K17P058] using h

theorem momentScalarAmp2622K17P058_radius_le :
    (momentScalarAmp2622K17P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarAmp2622K17P058Expected]

def momentScalarGrow2622K17P058Input : RatPair2542 := (momentPanelGrowth2622K17P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K17P058Expected : RatState2542 :=
  ((((2753087918435403688533707780969681347621365648222613223106947911878238130297483635743729128498519 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((872488176896885207656522184144190791578673643843 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K17P058_replay :
    compactExp2620 momentScalarGrow2622K17P058Input 20 = momentScalarGrow2622K17P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K17P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K17P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K17P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K17P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K17P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K17P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K17P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K17P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K17P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K17P058] using h

theorem momentScalarGrow2622K17P058_radius_le :
    (momentScalarGrow2622K17P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarGrow2622K17P058Expected]

end ConnesWeilRH.Dev
