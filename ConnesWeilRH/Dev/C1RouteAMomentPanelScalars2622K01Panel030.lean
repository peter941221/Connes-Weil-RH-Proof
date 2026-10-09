import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P030 : ℚ := ((-28613052598189383259224214017081591373422575091062531 : ℚ) / 614644218863821622777750852743425080483229833625600)

def momentPanelGrowth2622K01P030 : ℚ := ((31426864170024536551798967127591702448569276273 : ℚ) / 35681192317648997026457149236237378409568665600)

theorem momentPanelPhase_owner2622K01P030 :
    (momentPanelPhase2622K01P030 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P030 :
    (momentPanelGrowth2622K01P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P030Input : RatPair2542 := (momentPanelPhase2622K01P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P030Expected : RatState2542 :=
  ((((12948711600128580684134318506714697212079444504427132798083397926090289849147 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4104397157456289641770858665 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P030_replay :
    compactExp2620 momentScalarAmp2622K01P030Input 20 = momentScalarAmp2622K01P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K01P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P030_replay] at h
  simpa only [momentPanelPhase_owner2622K01P030] using h

theorem momentScalarAmp2622K01P030_radius_le :
    (momentScalarAmp2622K01P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P030Expected]

def momentScalarGrow2622K01P030Input : RatPair2542 := (momentPanelGrowth2622K01P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P030Expected : RatState2542 :=
  ((((2576804334591771250938222405652791150397439035404179169077530472532171891623403367319230719043245 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6532969635356364814461597093940195519916870347413 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P030_replay :
    compactExp2620 momentScalarGrow2622K01P030Input 20 = momentScalarGrow2622K01P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P030] using h

theorem momentScalarGrow2622K01P030_radius_le :
    (momentScalarGrow2622K01P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P030Expected]

end ConnesWeilRH.Dev
