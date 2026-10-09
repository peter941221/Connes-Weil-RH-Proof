import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P152 : ℚ := ((-1215 : ℚ) / 26)

def momentPanelGrowth2622K06P152 : ℚ := ((981372961 : ℚ) / 909324025)

theorem momentPanelPhase_owner2622K06P152 :
    (momentPanelPhase2622K06P152 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (5 / 8) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P152 :
    (momentPanelGrowth2622K06P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P152Input : RatPair2542 := (momentPanelPhase2622K06P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P152Expected : RatState2542 :=
  ((((2707842555201457347464072458048047552723530297768024960963870852590038630437 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((13733422734765611966933761703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P152_replay :
    compactExp2620 momentScalarAmp2622K06P152Input 20 = momentScalarAmp2622K06P152Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622K06P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P152]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P152 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P152_replay] at h
  simpa only [momentPanelPhase_owner2622K06P152] using h

theorem momentScalarAmp2622K06P152_radius_le :
    (momentScalarAmp2622K06P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P152Expected]

def momentScalarGrow2622K06P152Input : RatPair2542 := (momentPanelGrowth2622K06P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P152Expected : RatState2542 :=
  ((((6284978138674372433252433555776384136174665047133194402844621192282253339240320825177062852524475 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7967148109821784594246709419887067842542202621381 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P152_replay :
    compactExp2620 momentScalarGrow2622K06P152Input 20 = momentScalarGrow2622K06P152Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P152_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P152] using h

theorem momentScalarGrow2622K06P152_radius_le :
    (momentScalarGrow2622K06P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P152Expected]

end ConnesWeilRH.Dev
