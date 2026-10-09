import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P161 : ℚ := ((-19068069 : ℚ) / 325850)

def momentPanelGrowth2622K06P161 : ℚ := ((4309351 : ℚ) / 2265025)

theorem momentPanelPhase_owner2622K06P161 :
    (momentPanelPhase2622K06P161 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (143 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P161, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P161 :
    (momentPanelGrowth2622K06P161 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P161, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P161Input : RatPair2542 := (momentPanelPhase2622K06P161 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P161Expected : RatState2542 :=
  ((((82334624505812190749742044561132301445788156734441260761305416563096667 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1261114500117386323621777 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P161_replay :
    compactExp2620 momentScalarAmp2622K06P161Input 20 = momentScalarAmp2622K06P161Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P161_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (143 / 200) 0) -
      (momentScalarAmp2622K06P161Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P161]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P161 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P161 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P161Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P161_replay] at h
  simpa only [momentPanelPhase_owner2622K06P161] using h

theorem momentScalarAmp2622K06P161_radius_le :
    (momentScalarAmp2622K06P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P161Expected]

def momentScalarGrow2622K06P161Input : RatPair2542 := (momentPanelGrowth2622K06P161 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P161Expected : RatState2542 :=
  ((((14317621840199237039126832398097946231124847365246826424801383076860471758636411045131663468992431 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2268713623532337905845295797383889115122814470755 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P161_replay :
    compactExp2620 momentScalarGrow2622K06P161Input 20 = momentScalarGrow2622K06P161Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P161_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P161Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P161]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P161 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P161 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P161Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P161_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P161] using h

theorem momentScalarGrow2622K06P161_radius_le :
    (momentScalarGrow2622K06P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P161Expected]

end ConnesWeilRH.Dev
