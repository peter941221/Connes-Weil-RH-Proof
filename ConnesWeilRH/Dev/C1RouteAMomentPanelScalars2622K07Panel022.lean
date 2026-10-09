import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P022 : ℚ := ((-4279318368520518936825178905406900875 : ℚ) / 70663915059122419757032223480479744)

def momentPanelGrowth2622K07P022 : ℚ := ((8899423329938149654387090424593025 : ℚ) / 5963028423473591104640491878088704)

theorem momentPanelPhase_owner2622K07P022 :
    (momentPanelPhase2622K07P022 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P022 :
    (momentPanelGrowth2622K07P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P022Input : RatPair2542 := (momentPanelPhase2622K07P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P022Expected : RatState2542 :=
  ((((10697139060044577253797940157322371165539520343246844054408466011040795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((607853164287761111999725 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P022_replay :
    compactExp2620 momentScalarAmp2622K07P022Input 20 = momentScalarAmp2622K07P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K07P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P022_replay] at h
  simpa only [momentPanelPhase_owner2622K07P022] using h

theorem momentScalarAmp2622K07P022_radius_le :
    (momentScalarAmp2622K07P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P022Expected]

def momentScalarGrow2622K07P022Input : RatPair2542 := (momentPanelGrowth2622K07P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P022Expected : RatState2542 :=
  ((((9500670197759213142569276715231854766302149961652347649593183526737075081540380773824413902512391 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12043513137269789554174971796598239039693603150321 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P022_replay :
    compactExp2620 momentScalarGrow2622K07P022Input 20 = momentScalarGrow2622K07P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P022] using h

theorem momentScalarGrow2622K07P022_radius_le :
    (momentScalarGrow2622K07P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P022Expected]

end ConnesWeilRH.Dev
