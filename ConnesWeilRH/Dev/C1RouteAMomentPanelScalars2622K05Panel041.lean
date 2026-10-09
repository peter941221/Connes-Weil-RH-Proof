import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P041 : ℚ := ((-825451788340259316189410095646807399701 : ℚ) / 20681973072843608331299012136350515200)

def momentPanelGrowth2622K05P041 : ℚ := ((10213847817525979557836409430244303742763 : ℚ) / 19520061772722576365806994333466466713600)

theorem momentPanelPhase_owner2622K05P041 :
    (momentPanelPhase2622K05P041 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-97 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P041 :
    (momentPanelGrowth2622K05P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P041Input : RatPair2542 := (momentPanelPhase2622K05P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P041Expected : RatState2542 :=
  ((((9912581733289297391562369028456246095841012560709370458147386385694277191239103 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3141542723832217627326719965313 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P041_replay :
    compactExp2620 momentScalarAmp2622K05P041Input 20 = momentScalarAmp2622K05P041Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622K05P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P041]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P041 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P041_replay] at h
  simpa only [momentPanelPhase_owner2622K05P041] using h

theorem momentScalarAmp2622K05P041_radius_le :
    (momentScalarAmp2622K05P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P041Expected]

def momentScalarGrow2622K05P041Input : RatPair2542 := (momentPanelGrowth2622K05P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P041Expected : RatState2542 :=
  ((((1802240144447825530578355013912473100103543709714011200542062922847534015920678930746748916050123 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1142304830411942106595262324172531199766053182749 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P041_replay :
    compactExp2620 momentScalarGrow2622K05P041Input 20 = momentScalarGrow2622K05P041Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P041_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P041] using h

theorem momentScalarGrow2622K05P041_radius_le :
    (momentScalarGrow2622K05P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P041Expected]

end ConnesWeilRH.Dev
