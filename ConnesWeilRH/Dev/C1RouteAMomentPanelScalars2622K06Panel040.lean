import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P040 : ℚ := ((-62989701 : ℚ) / 1509950)

def momentPanelGrowth2622K06P040 : ℚ := ((43 : ℚ) / 75)

theorem momentPanelPhase_owner2622K06P040 :
    (momentPanelPhase2622K06P040 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P040 :
    (momentPanelGrowth2622K06P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P040Input : RatPair2542 := (momentPanelPhase2622K06P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P040Expected : RatState2542 :=
  ((((1630758774876794285651082557635349749096586919072906520544334369097144218389615 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1033658500898946476517912639293 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P040_replay :
    compactExp2620 momentScalarAmp2622K06P040Input 20 = momentScalarAmp2622K06P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K06P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P040_replay] at h
  simpa only [momentPanelPhase_owner2622K06P040] using h

theorem momentScalarAmp2622K06P040_radius_le :
    (momentScalarAmp2622K06P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P040Expected]

def momentScalarGrow2622K06P040Input : RatPair2542 := (momentPanelGrowth2622K06P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P040Expected : RatState2542 :=
  ((((29606300699563520262006653706344836900896296256459147265585691975515432389846748123689580449405 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((2401947157228833338390260955360568160877768279401 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P040_replay :
    compactExp2620 momentScalarGrow2622K06P040Input 20 = momentScalarGrow2622K06P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P040] using h

theorem momentScalarGrow2622K06P040_radius_le :
    (momentScalarGrow2622K06P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P040Expected]

end ConnesWeilRH.Dev
