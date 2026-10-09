import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P037 : ℚ := ((-504339 : ℚ) / 11590)

def momentPanelGrowth2622K06P037 : ℚ := ((282236827 : ℚ) / 430920675)

theorem momentPanelPhase_owner2622K06P037 :
    (momentPanelPhase2622K06P037 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P037 :
    (momentPanelGrowth2622K06P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P037Input : RatPair2542 := (momentPanelPhase2622K06P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P037Expected : RatState2542 :=
  ((((134970425204272048267907591566216109353964271183231200067786761312039504408667 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((171103649907644257569527756851 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P037_replay :
    compactExp2620 momentScalarAmp2622K06P037Input 20 = momentScalarAmp2622K06P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K06P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P037_replay] at h
  simpa only [momentPanelPhase_owner2622K06P037] using h

theorem momentScalarAmp2622K06P037_radius_le :
    (momentScalarAmp2622K06P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P037Expected]

def momentScalarGrow2622K06P037Input : RatPair2542 := (momentPanelGrowth2622K06P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P037Expected : RatState2542 :=
  ((((4111924728785068620229433312841760468090712029960352249516550468565666825231641133743769315709081 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2606240297356460306336420685971340626090663875809 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P037_replay :
    compactExp2620 momentScalarGrow2622K06P037Input 20 = momentScalarGrow2622K06P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P037] using h

theorem momentScalarGrow2622K06P037_radius_le :
    (momentScalarGrow2622K06P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P037Expected]

end ConnesWeilRH.Dev
