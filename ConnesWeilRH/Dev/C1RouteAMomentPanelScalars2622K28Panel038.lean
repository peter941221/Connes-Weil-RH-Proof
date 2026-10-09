import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P038 : ℚ := ((-827145871734626018550221691900160569579 : ℚ) / 19870676688697541514341122084909875200)

def momentPanelGrowth2622K28P038 : ℚ := ((660739174359222232834477654665694627 : ℚ) / 1098292480037737953456743657137766400)

theorem momentPanelPhase_owner2622K28P038 :
    (momentPanelPhase2622K28P038 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-103 / 200) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P038 :
    (momentPanelGrowth2622K28P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P038Input : RatPair2542 := (momentPanelPhase2622K28P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P038Expected : RatState2542 :=
  ((((1784259307067669015733942090374631415222969941221386508044182186498600188365529 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((565477397753835308149926797045 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K28P038_replay :
    compactExp2620 momentScalarAmp2622K28P038Input 20 = momentScalarAmp2622K28P038Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622K28P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P038]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P038 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P038_replay] at h
  simpa only [momentPanelPhase_owner2622K28P038] using h

theorem momentScalarAmp2622K28P038_radius_le :
    (momentScalarAmp2622K28P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P038Expected]

def momentScalarGrow2622K28P038Input : RatPair2542 := (momentPanelGrowth2622K28P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P038Expected : RatState2542 :=
  ((((3898277136682950579838848746325044994876914995281749355585538623369199761836510934195656659112051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1235412629242076023704218738980822140214150384161 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K28P038_replay :
    compactExp2620 momentScalarGrow2622K28P038Input 20 = momentScalarGrow2622K28P038Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P038_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P038] using h

theorem momentScalarGrow2622K28P038_radius_le :
    (momentScalarGrow2622K28P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P038Expected]

end ConnesWeilRH.Dev
