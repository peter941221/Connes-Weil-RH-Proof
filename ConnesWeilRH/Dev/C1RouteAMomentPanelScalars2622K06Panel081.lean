import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P081 : ℚ := ((-20225029 : ℚ) / 661850)

def momentPanelGrowth2622K06P081 : ℚ := ((233386561 : ℚ) / 2459664025)

theorem momentPanelPhase_owner2622K06P081 :
    (momentPanelPhase2622K06P081 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P081 :
    (momentPanelGrowth2622K06P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P081Input : RatPair2542 := (momentPanelPhase2622K06P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P081Expected : RatState2542 :=
  ((((114363026421130736836282762597743118490801788921592432208253293928756785280094336559 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((144976584035454566552422347960100801 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P081_replay :
    compactExp2620 momentScalarAmp2622K06P081Input 20 = momentScalarAmp2622K06P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K06P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P081_replay] at h
  simpa only [momentPanelPhase_owner2622K06P081] using h

theorem momentScalarAmp2622K06P081_radius_le :
    (momentScalarAmp2622K06P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P081Expected]

def momentScalarGrow2622K06P081Input : RatPair2542 := (momentPanelGrowth2622K06P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P081Expected : RatState2542 :=
  ((((2348588234929593063445184639216305973630652093337853757359945387114652561883046530648729934481085 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2977189016291886975261567242094792232594621935865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P081_replay :
    compactExp2620 momentScalarGrow2622K06P081Input 20 = momentScalarGrow2622K06P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P081] using h

theorem momentScalarGrow2622K06P081_radius_le :
    (momentScalarGrow2622K06P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P081Expected]

end ConnesWeilRH.Dev
