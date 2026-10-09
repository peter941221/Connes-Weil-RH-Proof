import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P141 : ℚ := ((-18990909 : ℚ) / 489850)

def momentPanelGrowth2622K06P141 : ℚ := ((1084937 : ℚ) / 1732800)

theorem momentPanelPhase_owner2622K06P141 :
    (momentPanelPhase2622K06P141 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (103 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P141 :
    (momentPanelGrowth2622K06P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P141Input : RatPair2542 := (momentPanelPhase2622K06P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P141Expected : RatState2542 :=
  ((((31082202083301808410137913265834891293824205704030766413682712044393807131015135 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19701415676219985568056933006655 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P141_replay :
    compactExp2620 momentScalarAmp2622K06P141Input 20 = momentScalarAmp2622K06P141Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622K06P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P141]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P141 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P141_replay] at h
  simpa only [momentPanelPhase_owner2622K06P141] using h

theorem momentScalarAmp2622K06P141_radius_le :
    (momentScalarAmp2622K06P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P141Expected]

def momentScalarGrow2622K06P141Input : RatPair2542 := (momentPanelGrowth2622K06P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P141Expected : RatState2542 :=
  ((((3995012450388403766734083202709390904726273379218200460020399288733523752582359637091040804504107 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((316517306669382990395158348478676115132746488903 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P141_replay :
    compactExp2620 momentScalarGrow2622K06P141Input 20 = momentScalarGrow2622K06P141Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P141_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P141] using h

theorem momentScalarGrow2622K06P141_radius_le :
    (momentScalarGrow2622K06P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P141Expected]

end ConnesWeilRH.Dev
