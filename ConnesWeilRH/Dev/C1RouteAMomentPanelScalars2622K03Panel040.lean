import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P040 : ℚ := ((-220033681776420089292335122370534200643115154517510925 : ℚ) / 5516985993219492153354134782899878863823688358166528)

def momentPanelGrowth2622K03P040 : ℚ := ((734806924159535908826659701413194244339169597863 : ℚ) / 1370157784997721485815954530671515330927436759040)

theorem momentPanelPhase_owner2622K03P040 :
    (momentPanelPhase2622K03P040 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P040 :
    (momentPanelGrowth2622K03P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P040Input : RatPair2542 := (momentPanelPhase2622K03P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P040Expected : RatState2542 :=
  ((((10201242968917413155080052619108774228142160830369498668341562595377680495507533 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3233026514538966816646948218315 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P040_replay :
    compactExp2620 momentScalarAmp2622K03P040Input 20 = momentScalarAmp2622K03P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K03P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P040_replay] at h
  simpa only [momentPanelPhase_owner2622K03P040] using h

theorem momentScalarAmp2622K03P040_radius_le :
    (momentScalarAmp2622K03P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P040Expected]

def momentScalarGrow2622K03P040Input : RatPair2542 := (momentPanelGrowth2622K03P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P040Expected : RatState2542 :=
  ((((1825904214852080819469063204254454531934010005350878210881533251727265195318461511183405579407377 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2314607390111437937348920556403169267686800208877 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P040_replay :
    compactExp2620 momentScalarGrow2622K03P040Input 20 = momentScalarGrow2622K03P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P040] using h

theorem momentScalarGrow2622K03P040_radius_le :
    (momentScalarGrow2622K03P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P040Expected]

end ConnesWeilRH.Dev
