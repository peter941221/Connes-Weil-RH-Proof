import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P149 : ℚ := ((-29095111668419716155735581836498546975 : ℚ) / 698769575665007349445830701305823232)

def momentPanelGrowth2622K07P149 : ℚ := ((38927714374939793992421619157275 : ℚ) / 40564819207303340847894502572032)

theorem momentPanelPhase_owner2622K07P149 :
    (momentPanelPhase2622K07P149 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P149 :
    (momentPanelGrowth2622K07P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P149Input : RatPair2542 := (momentPanelPhase2622K07P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P149Expected : RatState2542 :=
  ((((1764428379945367861586932973536326092414134968096476166400308402526161191468109 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((559192482552383713464782879461 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P149_replay :
    compactExp2620 momentScalarAmp2622K07P149Input 20 = momentScalarAmp2622K07P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K07P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P149_replay] at h
  simpa only [momentPanelPhase_owner2622K07P149] using h

theorem momentScalarAmp2622K07P149_radius_le :
    (momentScalarAmp2622K07P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P149Expected]

def momentScalarGrow2622K07P149Input : RatPair2542 := (momentPanelGrowth2622K07P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P149Expected : RatState2542 :=
  ((((2788277219870464197836308988819711330849873968340160339818645381317892889897604899909616668975137 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((883639514147843385738226076481305698020965562695 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P149_replay :
    compactExp2620 momentScalarGrow2622K07P149Input 20 = momentScalarGrow2622K07P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P149] using h

theorem momentScalarGrow2622K07P149_radius_le :
    (momentScalarGrow2622K07P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P149Expected]

end ConnesWeilRH.Dev
