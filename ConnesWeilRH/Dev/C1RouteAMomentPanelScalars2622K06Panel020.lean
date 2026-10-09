import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P020 : ℚ := ((-20958127 : ℚ) / 344650)

def momentPanelGrowth2622K06P020 : ℚ := ((35867 : ℚ) / 21675)

theorem momentPanelPhase_owner2622K06P020 :
    (momentPanelPhase2622K06P020 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-139 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P020 :
    (momentPanelGrowth2622K06P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P020Input : RatPair2542 := (momentPanelPhase2622K06P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P020Expected : RatState2542 :=
  ((((8321487056518875964848715228596507496025095408918405945132927324275693 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((607100247265104099476287 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P020_replay :
    compactExp2620 momentScalarAmp2622K06P020Input 20 = momentScalarAmp2622K06P020Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622K06P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P020]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P020 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P020_replay] at h
  simpa only [momentPanelPhase_owner2622K06P020] using h

theorem momentScalarAmp2622K06P020_radius_le :
    (momentScalarAmp2622K06P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P020Expected]

def momentScalarGrow2622K06P020Input : RatPair2542 := (momentPanelGrowth2622K06P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P020Expected : RatState2542 :=
  ((((11175148223213755349088704029486696243292532200031055218067249589678405574480034884225429786279043 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14166160997082129231845184140675809461025117130033 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P020_replay :
    compactExp2620 momentScalarGrow2622K06P020Input 20 = momentScalarGrow2622K06P020Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P020_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P020] using h

theorem momentScalarGrow2622K06P020_radius_le :
    (momentScalarGrow2622K06P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P020Expected]

end ConnesWeilRH.Dev
