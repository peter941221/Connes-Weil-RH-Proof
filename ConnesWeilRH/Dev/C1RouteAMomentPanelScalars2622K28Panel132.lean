import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P132 : ℚ := ((-6373686013748317420824684872040793699 : ℚ) / 177268259935915599505298976239779840)

def momentPanelGrowth2622K28P132 : ℚ := ((9069280857101648275995212159826149427523 : ℚ) / 22458982924291703410236951044810185113600)

theorem momentPanelPhase_owner2622K28P132 :
    (momentPanelPhase2622K28P132 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P132 :
    (momentPanelGrowth2622K28P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P132Input : RatPair2542 := (momentPanelPhase2622K28P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P132Expected : RatState2542 :=
  ((((518234692737089367431194690924163912371747452811643161685028228320122077086512019 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((41060190512597579243240824590375 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K28P132_replay :
    compactExp2620 momentScalarAmp2622K28P132Input 20 = momentScalarAmp2622K28P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K28P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P132_replay] at h
  simpa only [momentPanelPhase_owner2622K28P132] using h

theorem momentScalarAmp2622K28P132_radius_le :
    (momentScalarAmp2622K28P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P132Expected]

def momentScalarGrow2622K28P132Input : RatPair2542 := (momentPanelGrowth2622K28P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P132Expected : RatState2542 :=
  ((((3198698948799018079643625078609174858202656695597234832876047522331669911231101953389063916825701 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2027415540422584598377872155170412557687855412589 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K28P132_replay :
    compactExp2620 momentScalarGrow2622K28P132Input 20 = momentScalarGrow2622K28P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P132] using h

theorem momentScalarGrow2622K28P132_radius_le :
    (momentScalarGrow2622K28P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P132Expected]

end ConnesWeilRH.Dev
