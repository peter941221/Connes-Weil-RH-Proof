import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P027 : ℚ := ((-57244910606069644657711080739572835 : ℚ) / 1054685299389886862045257066872832)

def momentPanelGrowth2622K07P027 : ℚ := ((1652473113460041375543434465576456838075 : ℚ) / 1475462586999295331830173674166919626752)

theorem momentPanelPhase_owner2622K07P027 :
    (momentPanelPhase2622K07P027 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-5 / 8) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P027 :
    (momentPanelGrowth2622K07P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P027Input : RatPair2542 := (momentPanelPhase2622K07P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P027Expected : RatState2542 :=
  ((((1430333296689353961115158592384706795848918638777331311253415476365661843 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417719627903301456629111 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P027_replay :
    compactExp2620 momentScalarAmp2622K07P027Input 20 = momentScalarAmp2622K07P027Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622K07P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P027]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P027 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P027_replay] at h
  simpa only [momentPanelPhase_owner2622K07P027] using h

theorem momentScalarAmp2622K07P027_radius_le :
    (momentScalarAmp2622K07P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P027Expected]

def momentScalarGrow2622K07P027Input : RatPair2542 := (momentPanelGrowth2622K07P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P027Expected : RatState2542 :=
  ((((6546289258575775378613954880425322695576069131225790530637634549132978155005794500723969206360899 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4149199322245863806229682883529373283957053908659 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P027_replay :
    compactExp2620 momentScalarGrow2622K07P027Input 20 = momentScalarGrow2622K07P027Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P027_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P027] using h

theorem momentScalarGrow2622K07P027_radius_le :
    (momentScalarGrow2622K07P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P027Expected]

end ConnesWeilRH.Dev
