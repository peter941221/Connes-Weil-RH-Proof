import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P028 : ℚ := ((-383886587360548985896583530429631944978407630497837091 : ℚ) / 7099415473057985640360126069235678707395058257100800)

def momentPanelGrowth2622K04P028 : ℚ := ((121282646855119461794042390024276143201898277708316189 : ℚ) / 112682204412520426781468418088216255664013313887436800)

theorem momentPanelPhase_owner2622K04P028 :
    (momentPanelPhase2622K04P028 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P028 :
    (momentPanelGrowth2622K04P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P028Input : RatPair2542 := (momentPanelPhase2622K04P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P028Expected : RatState2542 :=
  ((((7014545670163193929622427154222938275847538173471425995086288027756289327 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2827575805655224160310143 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P028_replay :
    compactExp2620 momentScalarAmp2622K04P028Input 20 = momentScalarAmp2622K04P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K04P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P028_replay] at h
  simpa only [momentPanelPhase_owner2622K04P028] using h

theorem momentScalarAmp2622K04P028_radius_le :
    (momentScalarAmp2622K04P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P028Expected]

def momentScalarGrow2622K04P028Input : RatPair2542 := (momentPanelGrowth2622K04P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P028Expected : RatState2542 :=
  ((((3133361635820170503199195224841832201609831818623891810094468794059980936825566705713740609667637 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1986001840630759910775543602745608737344593435839 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P028_replay :
    compactExp2620 momentScalarGrow2622K04P028Input 20 = momentScalarGrow2622K04P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P028] using h

theorem momentScalarGrow2622K04P028_radius_le :
    (momentScalarGrow2622K04P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P028Expected]

end ConnesWeilRH.Dev
