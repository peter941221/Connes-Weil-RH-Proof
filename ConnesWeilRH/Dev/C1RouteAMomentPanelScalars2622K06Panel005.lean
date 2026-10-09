import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P005 : ℚ := ((-20644397 : ℚ) / 190650)

def momentPanelGrowth2622K06P005 : ℚ := ((684107 : ℚ) / 102675)

theorem momentPanelPhase_owner2622K06P005 :
    (momentPanelPhase2622K06P005 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-169 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P005, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P005 :
    (momentPanelGrowth2622K06P005 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P005, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P005Input : RatPair2542 := (momentPanelPhase2622K06P005 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P005Expected : RatState2542 :=
  ((((20060214316857150943165015724838632978604520296385 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412393 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P005_replay :
    compactExp2620 momentScalarAmp2622K06P005Input 20 = momentScalarAmp2622K06P005Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P005_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-169 / 200) 0) -
      (momentScalarAmp2622K06P005Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P005]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P005 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P005 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P005Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P005_replay] at h
  simpa only [momentPanelPhase_owner2622K06P005] using h

theorem momentScalarAmp2622K06P005_radius_le :
    (momentScalarAmp2622K06P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P005Expected]

def momentScalarGrow2622K06P005Input : RatPair2542 := (momentPanelGrowth2622K06P005 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P005Expected : RatState2542 :=
  ((((1671986813624953314253671076236656777160014486157747698144086645807243879144551215095665375598572795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1059740810129033002306949181307159969380994507352375 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P005_replay :
    compactExp2620 momentScalarGrow2622K06P005Input 20 = momentScalarGrow2622K06P005Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P005_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P005Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P005]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P005 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P005 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P005Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P005_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P005] using h

theorem momentScalarGrow2622K06P005_radius_le :
    (momentScalarGrow2622K06P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P005Expected]

end ConnesWeilRH.Dev
