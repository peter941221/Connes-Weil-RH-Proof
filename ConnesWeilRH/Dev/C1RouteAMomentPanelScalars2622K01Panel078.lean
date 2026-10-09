import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P078 : ℚ := ((-28565059702559968652368814883587627285885155211688803 : ℚ) / 938914894646615707754193425002350375469389866598400)

def momentPanelGrowth2622K01P078 : ℚ := ((16074141547605980759588461955761267638862691182617 : ℚ) / 211553789251340903369864437821651416590332618342400)

theorem momentPanelPhase_owner2622K01P078 :
    (momentPanelPhase2622K01P078 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P078 :
    (momentPanelGrowth2622K01P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P078Input : RatPair2542 := (momentPanelPhase2622K01P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P078Expected : RatState2542 :=
  ((((65436277435733210615885369002440392588789374679380043888811805112229012547465539173 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((41476371566490156184454136683157029 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P078_replay :
    compactExp2620 momentScalarAmp2622K01P078Input 20 = momentScalarAmp2622K01P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K01P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P078_replay] at h
  simpa only [momentPanelPhase_owner2622K01P078] using h

theorem momentScalarAmp2622K01P078_radius_le :
    (momentScalarAmp2622K01P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P078Expected]

def momentScalarGrow2622K01P078Input : RatPair2542 := (momentPanelGrowth2622K01P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P078Expected : RatState2542 :=
  ((((2304607078891953871694824140304292598070455979611285108098976561156479725119408883417324851891679 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((730359083789017175320064259017880952753276411679 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P078_replay :
    compactExp2620 momentScalarGrow2622K01P078Input 20 = momentScalarGrow2622K01P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P078] using h

theorem momentScalarGrow2622K01P078_radius_le :
    (momentScalarGrow2622K01P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P078Expected]

end ConnesWeilRH.Dev
