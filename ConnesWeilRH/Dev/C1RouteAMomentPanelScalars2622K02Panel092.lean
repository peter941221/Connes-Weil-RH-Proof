import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P092 : ℚ := ((-910328346821273481551588087979433762373764885057093 : ℚ) / 30428920808491064664162656868663236307680158023680)

def momentPanelGrowth2622K02P092 : ℚ := ((839377513779913744371153654406272457247578266889371999 : ℚ) / 14246798029297202450998847119161212992283181501015654400)

theorem momentPanelPhase_owner2622K02P092 :
    (momentPanelPhase2622K02P092 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (1 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P092, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P092 :
    (momentPanelGrowth2622K02P092 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P092, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P092Input : RatPair2542 := (momentPanelPhase2622K02P092 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P092Expected : RatState2542 :=
  ((((217273020256248849070815786990205233719953990608085667622563397113272903400202300679 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((68858533186313510091291810746466723 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P092_replay :
    compactExp2620 momentScalarAmp2622K02P092Input 20 = momentScalarAmp2622K02P092Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P092_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (1 / 40) 0) -
      (momentScalarAmp2622K02P092Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P092]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P092 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P092 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P092Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P092_replay] at h
  simpa only [momentPanelPhase_owner2622K02P092] using h

theorem momentScalarAmp2622K02P092_radius_le :
    (momentScalarAmp2622K02P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P092Expected]

def momentScalarGrow2622K02P092Input : RatPair2542 := (momentPanelGrowth2622K02P092 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P092Expected : RatState2542 :=
  ((((283201741976882670466336397474254268382105463806226087375939989323017059128746373288191624572883 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1436003352125179397610321602370562432157625855529 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P092_replay :
    compactExp2620 momentScalarGrow2622K02P092Input 20 = momentScalarGrow2622K02P092Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P092_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P092Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P092]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P092 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P092 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P092Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P092_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P092] using h

theorem momentScalarGrow2622K02P092_radius_le :
    (momentScalarGrow2622K02P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P092Expected]

end ConnesWeilRH.Dev
