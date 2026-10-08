import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P151 : ℚ := ((-301192305138311757011393734906125720485310749022162909 : ℚ) / 7099415473057985640360126069235678707395058257100800)

def momentPanelGrowth2622K04P151 : ℚ := ((121282646855119461794042390024276143201898277708316189 : ℚ) / 112682204412520426781468418088216255664013313887436800)

theorem momentPanelPhase_owner2622K04P151 :
    (momentPanelPhase2622K04P151 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (123 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P151, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P151 :
    (momentPanelGrowth2622K04P151 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P151, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P151Input : RatPair2542 := (momentPanelPhase2622K04P151 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P151Expected : RatState2542 :=
  ((((802933283949941965515733943190870395490900431343957761277298978156673034870477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((508941229679748904847008578201 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P151_replay :
    compactExp2620 momentScalarAmp2622K04P151Input 20 = momentScalarAmp2622K04P151Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P151_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (123 / 200) 0) -
      (momentScalarAmp2622K04P151Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P151]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P151 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P151 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P151Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P151_replay] at h
  simpa only [momentPanelPhase_owner2622K04P151] using h

theorem momentScalarAmp2622K04P151_radius_le :
    (momentScalarAmp2622K04P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P151Expected]

def momentScalarGrow2622K04P151Input : RatPair2542 := (momentPanelGrowth2622K04P151 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P151Expected : RatState2542 :=
  ((((3133361635820170503199195224841832201609831818623891810094468794059980936825566705713740609667637 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1986001840630759910775543602745608737344593435839 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P151_replay :
    compactExp2620 momentScalarGrow2622K04P151Input 20 = momentScalarGrow2622K04P151Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P151_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P151Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P151]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P151 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P151 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P151Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P151_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P151] using h

theorem momentScalarGrow2622K04P151_radius_le :
    (momentScalarGrow2622K04P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P151Expected]

end ConnesWeilRH.Dev
