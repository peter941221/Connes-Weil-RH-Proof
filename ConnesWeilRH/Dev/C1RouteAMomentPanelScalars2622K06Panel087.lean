import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P087 : ℚ := ((-160533 : ℚ) / 5330)

def momentPanelGrowth2622K06P087 : ℚ := ((144820081 : ℚ) / 2495502025)

theorem momentPanelPhase_owner2622K06P087 :
    (momentPanelPhase2622K06P087 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P087 :
    (momentPanelGrowth2622K06P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P087Input : RatPair2542 := (momentPanelPhase2622K06P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P087Expected : RatState2542 :=
  ((((22186898985830131023797082698308257065882526288186136927732675386583979697441437723 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((112504174733643501479267781941774083 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P087_replay :
    compactExp2620 momentScalarAmp2622K06P087Input 20 = momentScalarAmp2622K06P087Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622K06P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P087]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P087 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P087_replay] at h
  simpa only [momentPanelPhase_owner2622K06P087] using h

theorem momentScalarAmp2622K06P087_radius_le :
    (momentScalarAmp2622K06P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P087Expected]

def momentScalarGrow2622K06P087Input : RatPair2542 := (momentPanelGrowth2622K06P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P087Expected : RatState2542 :=
  ((((2263610931540302113631456706044834191942255579624812495627951346291012485207964274626398225374931 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1434733798621139806405139864081746808425466947049 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P087_replay :
    compactExp2620 momentScalarGrow2622K06P087Input 20 = momentScalarGrow2622K06P087Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P087_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P087] using h

theorem momentScalarGrow2622K06P087_radius_le :
    (momentScalarGrow2622K06P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P087Expected]

end ConnesWeilRH.Dev
