import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P120 : ℚ := ((-109875325290660289957576364650431823513594513823399033 : ℚ) / 3451941269578634568327570445710548936855310984806400)

def momentPanelGrowth2622K02P120 : ℚ := ((1043813126602573445403566209709521249277300828668369253 : ℚ) / 3887038727773431332240105664297406143828186761055436800)

theorem momentPanelPhase_owner2622K02P120 :
    (momentPanelPhase2622K02P120 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (61 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P120 :
    (momentPanelGrowth2622K02P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P120Input : RatPair2542 := (momentPanelPhase2622K02P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P120Expected : RatState2542 :=
  ((((32062758976942672679340340686603619404311418406946992977703518363783950148403811519 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20322804731041471961155635330486409 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P120_replay :
    compactExp2620 momentScalarAmp2622K02P120Input 20 = momentScalarAmp2622K02P120Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622K02P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P120]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P120 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P120_replay] at h
  simpa only [momentPanelPhase_owner2622K02P120] using h

theorem momentScalarAmp2622K02P120_radius_le :
    (momentScalarAmp2622K02P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P120Expected]

def momentScalarGrow2622K02P120Input : RatPair2542 := (momentPanelGrowth2622K02P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P120Expected : RatState2542 :=
  ((((2793976079431236566601570048929498095650628253849365862063708008239394739016671263119452099268633 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1770892273537445303849309610042217220817146222127 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P120_replay :
    compactExp2620 momentScalarGrow2622K02P120Input 20 = momentScalarGrow2622K02P120Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P120_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P120] using h

theorem momentScalarGrow2622K02P120_radius_le :
    (momentScalarGrow2622K02P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P120Expected]

end ConnesWeilRH.Dev
