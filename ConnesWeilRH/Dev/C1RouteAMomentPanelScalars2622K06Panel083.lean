import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P083 : ℚ := ((-20172601 : ℚ) / 663850)

def momentPanelGrowth2622K06P083 : ℚ := ((68007467 : ℚ) / 825186675)

theorem momentPanelPhase_owner2622K06P083 :
    (momentPanelPhase2622K06P083 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P083 :
    (momentPanelGrowth2622K06P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P083Input : RatPair2542 := (momentPanelPhase2622K06P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P083Expected : RatState2542 :=
  ((((135696049682227035656243459958728398378274551042053404077123622050991282993357540681 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10751260239366037604398614128399765 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K06P083_replay :
    compactExp2620 momentScalarAmp2622K06P083Input 20 = momentScalarAmp2622K06P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K06P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P083_replay] at h
  simpa only [momentPanelPhase_owner2622K06P083] using h

theorem momentScalarAmp2622K06P083_radius_le :
    (momentScalarAmp2622K06P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P083Expected]

def momentScalarGrow2622K06P083Input : RatPair2542 := (momentPanelGrowth2622K06P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P083Expected : RatState2542 :=
  ((((2319481100074880709381864972562386629809388086665642850832815548277210347843163031048075779962865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1470145688815329354633664756375959333216878584029 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P083_replay :
    compactExp2620 momentScalarGrow2622K06P083Input 20 = momentScalarGrow2622K06P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P083] using h

theorem momentScalarGrow2622K06P083_radius_le :
    (momentScalarGrow2622K06P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P083Expected]

end ConnesWeilRH.Dev
