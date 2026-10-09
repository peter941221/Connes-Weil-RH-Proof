import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P157 : ℚ := ((-3509126919281722505970565588423243125 : ℚ) / 70663915059122419757032223480479744)

def momentPanelGrowth2622K07P157 : ℚ := ((8899423329938149654387090424593025 : ℚ) / 5963028423473591104640491878088704)

theorem momentPanelPhase_owner2622K07P157 :
    (momentPanelPhase2622K07P157 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P157, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P157 :
    (momentPanelGrowth2622K07P157 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P157, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P157Input : RatPair2542 := (momentPanelPhase2622K07P157 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P157Expected : RatState2542 :=
  ((((579161315421434979562410113581171842811632490096187963916657542794820230735 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((736626811256479555588462263 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P157_replay :
    compactExp2620 momentScalarAmp2622K07P157Input 20 = momentScalarAmp2622K07P157Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P157_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 40) 0) -
      (momentScalarAmp2622K07P157Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P157]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P157 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P157 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P157Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P157_replay] at h
  simpa only [momentPanelPhase_owner2622K07P157] using h

theorem momentScalarAmp2622K07P157_radius_le :
    (momentScalarAmp2622K07P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P157Expected]

def momentScalarGrow2622K07P157Input : RatPair2542 := (momentPanelGrowth2622K07P157 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P157Expected : RatState2542 :=
  ((((9500670197759213142569276715231854766302149961652347649593183526737075081540380773824413902512391 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12043513137269789554174971796598239039693603150321 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P157_replay :
    compactExp2620 momentScalarGrow2622K07P157Input 20 = momentScalarGrow2622K07P157Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P157_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P157Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P157]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P157 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P157 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P157Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P157_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P157] using h

theorem momentScalarGrow2622K07P157_radius_le :
    (momentScalarGrow2622K07P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P157Expected]

end ConnesWeilRH.Dev
