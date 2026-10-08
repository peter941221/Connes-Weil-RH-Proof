import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P072 : ℚ := ((-962352808418843317277639303636339986673006285449213 : ℚ) / 29515482285159250340285353848215559420395200184320)

def momentPanelGrowth2622K04P072 : ℚ := ((175428725463272757196818437116270497422394709981630647 : ℚ) / 835162693597817930756530490567785720974696121788006400)

theorem momentPanelPhase_owner2622K04P072 :
    (momentPanelPhase2622K04P072 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P072, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P072 :
    (momentPanelGrowth2622K04P072 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P072, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P072Input : RatPair2542 := (momentPanelPhase2622K04P072 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P072Expected : RatState2542 :=
  ((((14771328200194425619343014318065110875717446113312226638593152470334850750152144963 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((9362732656377697115440542528848733 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P072_replay :
    compactExp2620 momentScalarAmp2622K04P072Input 20 = momentScalarAmp2622K04P072Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P072_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 40) 0) -
      (momentScalarAmp2622K04P072Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P072]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P072 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P072 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P072Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P072_replay] at h
  simpa only [momentPanelPhase_owner2622K04P072] using h

theorem momentScalarAmp2622K04P072_radius_le :
    (momentScalarAmp2622K04P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P072Expected]

def momentScalarGrow2622K04P072Input : RatPair2542 := (momentPanelGrowth2622K04P072 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P072Expected : RatState2542 :=
  ((((2635260942224749951718855839787302006861932450706480613333844225023042564117331132206753651543873 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1670294722986976399155478384464717758638233783611 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P072_replay :
    compactExp2620 momentScalarGrow2622K04P072Input 20 = momentScalarGrow2622K04P072Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P072_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P072Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P072]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P072 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P072 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P072Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P072_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P072] using h

theorem momentScalarGrow2622K04P072_radius_le :
    (momentScalarGrow2622K04P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P072Expected]

end ConnesWeilRH.Dev
