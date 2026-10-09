import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P134 : ℚ := ((-72817741712658892119466579009858322901368730613161275 : ℚ) / 1953479625997418113044000239529401791147610835255296)

def momentPanelGrowth2622K03P134 : ℚ := ((3973571310872339725046424497966445574177321979051625 : ℚ) / 9295241757276875741207823266377604772700459469111296)

theorem momentPanelPhase_owner2622K03P134 :
    (momentPanelPhase2622K03P134 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (89 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P134, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P134 :
    (momentPanelGrowth2622K03P134 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P134, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P134Input : RatPair2542 := (momentPanelPhase2622K03P134 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P134Expected : RatState2542 :=
  ((((138316550324876830052136586801029066085049840619611804475059068639168178646973515 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((43835823410290525380247069678561 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P134_replay :
    compactExp2620 momentScalarAmp2622K03P134Input 20 = momentScalarAmp2622K03P134Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P134_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (89 / 200) 0) -
      (momentScalarAmp2622K03P134Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P134]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P134 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P134 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P134Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P134_replay] at h
  simpa only [momentPanelPhase_owner2622K03P134] using h

theorem momentScalarAmp2622K03P134_radius_le :
    (momentScalarAmp2622K03P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P134Expected]

def momentScalarGrow2622K03P134Input : RatPair2542 := (momentPanelGrowth2622K03P134 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P134Expected : RatState2542 :=
  ((((409414069640685068519614902487010258243531957426208781089723567498829939917646227244735013845985 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2075975118151924653664571283855639670427728681197 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P134_replay :
    compactExp2620 momentScalarGrow2622K03P134Input 20 = momentScalarGrow2622K03P134Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P134_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P134Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P134]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P134 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P134 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P134Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P134_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P134] using h

theorem momentScalarGrow2622K03P134_radius_le :
    (momentScalarGrow2622K03P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P134Expected]

end ConnesWeilRH.Dev
