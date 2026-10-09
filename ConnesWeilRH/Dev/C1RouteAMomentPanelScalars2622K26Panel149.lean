import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K26
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K26P149 : ℚ := ((-795197851154066107413898936770046139557 : ℚ) / 17469239391625183736145767532645580800)

def momentPanelGrowth2622K26P149 : ℚ := ((907023526282541655625368571645369 : ℚ) / 1014120480182583521197362564300800)

theorem momentPanelPhase_owner2622K26P149 :
    (momentPanelPhase2622K26P149 : ℝ) = momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K26P149 :
    (momentPanelGrowth2622K26P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K26P149Input : RatPair2542 := (momentPanelPhase2622K26P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K26P149Expected : RatState2542 :=
  ((((36354793022720778670679902597034679450009412137423177257024816333750144438029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((23044796850965632264306690869 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K26P149_replay :
    compactExp2620 momentScalarAmp2622K26P149Input 20 = momentScalarAmp2622K26P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K26P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K26P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K26P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K26P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K26P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K26P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K26P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K26P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K26P149_replay] at h
  simpa only [momentPanelPhase_owner2622K26P149] using h

theorem momentScalarAmp2622K26P149_radius_le :
    (momentScalarAmp2622K26P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarAmp2622K26P149Expected]

def momentScalarGrow2622K26P149Input : RatPair2542 := (momentPanelGrowth2622K26P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K26P149Expected : RatState2542 :=
  ((((5224311933203272147586526244690711679851387984037006903462189917619579738519518039893483441974977 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3311298254543419324652524336819471022261287896451 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K26P149_replay :
    compactExp2620 momentScalarGrow2622K26P149Input 20 = momentScalarGrow2622K26P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K26P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K26P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K26P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K26P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K26P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K26P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K26P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K26P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K26P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K26P149] using h

theorem momentScalarGrow2622K26P149_radius_le :
    (momentScalarGrow2622K26P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarGrow2622K26P149Expected]

end ConnesWeilRH.Dev
