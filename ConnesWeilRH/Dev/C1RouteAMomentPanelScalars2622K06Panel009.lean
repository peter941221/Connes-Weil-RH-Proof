import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P009 : ℚ := ((-20755573 : ℚ) / 234650)

def momentPanelGrowth2622K06P009 : ℚ := ((1226826721 : ℚ) / 295668025)

theorem momentPanelPhase_owner2622K06P009 :
    (momentPanelPhase2622K06P009 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-161 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P009 :
    (momentPanelGrowth2622K06P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P009Input : RatPair2542 := (momentPanelPhase2622K06P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P009Expected : RatState2542 :=
  ((((8218775630932704137506980070919179840448753402453709889741 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614634384563537 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P009_replay :
    compactExp2620 momentScalarAmp2622K06P009Input 20 = momentScalarAmp2622K06P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K06P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P009_replay] at h
  simpa only [momentPanelPhase_owner2622K06P009] using h

theorem momentScalarAmp2622K06P009_radius_le :
    (momentScalarAmp2622K06P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P009Expected]

def momentScalarGrow2622K06P009Input : RatPair2542 := (momentPanelGrowth2622K06P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P009Expected : RatState2542 :=
  ((((135404603251950910438757240884613182656900700035303713514217561606054710773900091791195936480256483 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((85822523682512728333428411297724802643201405766141 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P009_replay :
    compactExp2620 momentScalarGrow2622K06P009Input 20 = momentScalarGrow2622K06P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P009] using h

theorem momentScalarGrow2622K06P009_radius_le :
    (momentScalarGrow2622K06P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P009Expected]

end ConnesWeilRH.Dev
