import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P009 : ℚ := ((-823163941071805369402340348368192951437 : ℚ) / 9518534826993728929958445028527308800)

def momentPanelGrowth2622K20P009 : ℚ := ((49472014071916139501253758598092727225049 : ℚ) / 11993719979505444364398792983830121676800)

theorem momentPanelPhase_owner2622K20P009 :
    (momentPanelPhase2622K20P009 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-161 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P009 :
    (momentPanelGrowth2622K20P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P009Input : RatPair2542 := (momentPanelPhase2622K20P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P009Expected : RatState2542 :=
  ((((59124018601354633527879173839833666120086529165345336450097 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614666652498053 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K20P009_replay :
    compactExp2620 momentScalarAmp2622K20P009Input 20 = momentScalarAmp2622K20P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K20P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P009_replay] at h
  simpa only [momentPanelPhase_owner2622K20P009] using h

theorem momentScalarAmp2622K20P009_radius_le :
    (momentScalarAmp2622K20P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P009Expected]

def momentScalarGrow2622K20P009Input : RatPair2542 := (momentPanelGrowth2622K20P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P009Expected : RatState2542 :=
  ((((132125913401693637128255038637871313035896726614782407907020364350924426950415138233731686278825341 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((167488834570352106479578817606650642369519043219187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P009_replay :
    compactExp2620 momentScalarGrow2622K20P009Input 20 = momentScalarGrow2622K20P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P009] using h

theorem momentScalarGrow2622K20P009_radius_le :
    (momentScalarGrow2622K20P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P009Expected]

end ConnesWeilRH.Dev
