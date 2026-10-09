import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P142 : ℚ := ((-455661 : ℚ) / 11590)

def momentPanelGrowth2622K06P142 : ℚ := ((282236827 : ℚ) / 430920675)

theorem momentPanelPhase_owner2622K06P142 :
    (momentPanelPhase2622K06P142 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P142 :
    (momentPanelGrowth2622K06P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P142Input : RatPair2542 := (momentPanelPhase2622K06P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P142Expected : RatState2542 :=
  ((((18001364911813024388430614997133724795601046010034851443075675731710500164195619 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22820299054967767856554461677225 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P142_replay :
    compactExp2620 momentScalarAmp2622K06P142Input 20 = momentScalarAmp2622K06P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K06P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P142_replay] at h
  simpa only [momentPanelPhase_owner2622K06P142] using h

theorem momentScalarAmp2622K06P142_radius_le :
    (momentScalarAmp2622K06P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P142Expected]

def momentScalarGrow2622K06P142Input : RatPair2542 := (momentPanelGrowth2622K06P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P142Expected : RatState2542 :=
  ((((4111924728785068620229433312841760468090712029960352249516550468565666825231641133743769315709081 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2606240297356460306336420685971340626090663875809 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P142_replay :
    compactExp2620 momentScalarGrow2622K06P142Input 20 = momentScalarGrow2622K06P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P142] using h

theorem momentScalarGrow2622K06P142_radius_le :
    (momentScalarGrow2622K06P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P142Expected]

end ConnesWeilRH.Dev
