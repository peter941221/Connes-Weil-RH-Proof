import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P112 : ℚ := ((-2555538783196666135827543952895334272870620877437383 : ℚ) / 86719569808814122373101455503751324486615684874240)

def momentPanelGrowth2622K04P112 : ℚ := ((1060660639845365278399109045122788119895052386387838069 : ℚ) / 4267463036778048702776905439738352375460189577202892800)

theorem momentPanelPhase_owner2622K04P112 :
    (momentPanelPhase2622K04P112 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P112 :
    (momentPanelGrowth2622K04P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P112Input : RatPair2542 := (momentPanelPhase2622K04P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P112Expected : RatState2542 :=
  ((((339919144081549026793679413262676883110347088211274378145508765049376429788445361667 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((53863852137365151802643029193751089 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P112_replay :
    compactExp2620 momentScalarAmp2622K04P112Input 20 = momentScalarAmp2622K04P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K04P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P112_replay] at h
  simpa only [momentPanelPhase_owner2622K04P112] using h

theorem momentScalarAmp2622K04P112_radius_le :
    (momentScalarAmp2622K04P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P112Expected]

def momentScalarGrow2622K04P112Input : RatPair2542 := (momentPanelGrowth2622K04P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P112Expected : RatState2542 :=
  ((((1369338282587401657532777983077104187075700714825669785411996238368767843955299589687199797788675 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((867921042193720649027025187353459480912241912495 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P112_replay :
    compactExp2620 momentScalarGrow2622K04P112Input 20 = momentScalarGrow2622K04P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P112] using h

theorem momentScalarGrow2622K04P112_radius_le :
    (momentScalarGrow2622K04P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P112Expected]

end ConnesWeilRH.Dev
