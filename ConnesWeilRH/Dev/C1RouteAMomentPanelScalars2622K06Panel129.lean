import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P129 : ℚ := ((-19111013 : ℚ) / 562650)

def momentPanelGrowth2622K06P129 : ℚ := ((1397 : ℚ) / 3675)

theorem momentPanelPhase_owner2622K06P129 :
    (momentPanelPhase2622K06P129 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P129 :
    (momentPanelGrowth2622K06P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P129Input : RatPair2542 := (momentPanelPhase2622K06P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P129Expected : RatState2542 :=
  ((((3787206381786326920316500438775045376770911714706764437802455784484589431880581299 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4801009960033270065379366224852543 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P129_replay :
    compactExp2620 momentScalarAmp2622K06P129Input 20 = momentScalarAmp2622K06P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K06P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P129_replay] at h
  simpa only [momentPanelPhase_owner2622K06P129] using h

theorem momentScalarAmp2622K06P129_radius_le :
    (momentScalarAmp2622K06P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P129Expected]

def momentScalarGrow2622K06P129Input : RatPair2542 := (momentPanelGrowth2622K06P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P129Expected : RatState2542 :=
  ((((3123845909996272157287835783675051369416787239717225885917852358393830058266820698124537764755333 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1979971853622246814500260775680432855576259546675 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P129_replay :
    compactExp2620 momentScalarGrow2622K06P129Input 20 = momentScalarGrow2622K06P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P129] using h

theorem momentScalarGrow2622K06P129_radius_le :
    (momentScalarGrow2622K06P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P129Expected]

end ConnesWeilRH.Dev
