import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P147 : ℚ := ((-2911901713924496697510544756236886704954701581663625 : ℚ) / 65219510565891542724839435659964129752145989730304)

def momentPanelGrowth2622K03P147 : ℚ := ((66472371654564632778283798807536698665786758960682475 : ℚ) / 83801316414473641971178247814025086367117701569052672)

theorem momentPanelPhase_owner2622K03P147 :
    (momentPanelPhase2622K03P147 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P147 :
    (momentPanelGrowth2622K03P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P147Input : RatPair2542 := (momentPanelPhase2622K03P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P147Expected : RatState2542 :=
  ((((86965112611104333163988983381342583496453696354691376815253668145713218671413 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((27562122290173245300233612861 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P147_replay :
    compactExp2620 momentScalarAmp2622K03P147Input 20 = momentScalarAmp2622K03P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K03P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P147_replay] at h
  simpa only [momentPanelPhase_owner2622K03P147] using h

theorem momentScalarAmp2622K03P147_radius_le :
    (momentScalarAmp2622K03P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P147Expected]

def momentScalarGrow2622K03P147Input : RatPair2542 := (momentPanelGrowth2622K03P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P147Expected : RatState2542 :=
  ((((590197083242690701032774631478870026394651915059672415787611701566146960283295065564596594448515 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2992652483456230144312738937061484018094451155133 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P147_replay :
    compactExp2620 momentScalarGrow2622K03P147Input 20 = momentScalarGrow2622K03P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P147] using h

theorem momentScalarGrow2622K03P147_radius_le :
    (momentScalarGrow2622K03P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P147Expected]

end ConnesWeilRH.Dev
