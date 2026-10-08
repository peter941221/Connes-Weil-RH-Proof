import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P167 : ℚ := ((-824192592292949321550024634734843937503448060546219 : ℚ) / 12160150341854778186616596459709698561981001236480)

def momentPanelGrowth2622K04P167 : ℚ := ((430424207180073578960201231749422325911041682827596407 : ℚ) / 136793270584479289436138466284514356800981605705318400)

theorem momentPanelPhase_owner2622K04P167 :
    (momentPanelPhase2622K04P167 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (31 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P167 :
    (momentPanelGrowth2622K04P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P167Input : RatPair2542 := (momentPanelPhase2622K04P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P167Expected : RatState2542 :=
  ((((1958206862521933651022327547047632974085213907488996222467734633617 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208930784579759575492619 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P167_replay :
    compactExp2620 momentScalarAmp2622K04P167Input 20 = momentScalarAmp2622K04P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K04P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P167_replay] at h
  simpa only [momentPanelPhase_owner2622K04P167] using h

theorem momentScalarAmp2622K04P167_radius_le :
    (momentScalarAmp2622K04P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P167Expected]

def momentScalarGrow2622K04P167Input : RatPair2542 := (momentPanelGrowth2622K04P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P167Expected : RatState2542 :=
  ((((49672895303714155998898604908249338410073960415551495501458473031901154774656625034205225995829231 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15741921648822328271496739405096150087416301667367 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P167_replay :
    compactExp2620 momentScalarGrow2622K04P167Input 20 = momentScalarGrow2622K04P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P167] using h

theorem momentScalarGrow2622K04P167_radius_le :
    (momentScalarGrow2622K04P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P167Expected]

end ConnesWeilRH.Dev
