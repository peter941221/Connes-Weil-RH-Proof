import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P096 : ℚ := ((-808826244940658899771958479541052897511 : ℚ) / 26928955230768322821874765532443443200)

def momentPanelGrowth2622K05P096 : ℚ := ((1892147385634496820600283834270855511563 : ℚ) / 33473548283650779550665745328194034073600)

theorem momentPanelPhase_owner2622K05P096 :
    (momentPanelPhase2622K05P096 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P096, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P096 :
    (momentPanelGrowth2622K05P096 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P096, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P096Input : RatPair2542 := (momentPanelPhase2622K05P096 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P096Expected : RatState2542 :=
  ((((24111861891300969117338871952366737756461400938565842855292811681387245165875871793 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((122265166928359485040832742398315995 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P096_replay :
    compactExp2620 momentScalarAmp2622K05P096Input 20 = momentScalarAmp2622K05P096Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P096_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 200) 0) -
      (momentScalarAmp2622K05P096Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P096]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P096 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P096 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P096Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P096_replay] at h
  simpa only [momentPanelPhase_owner2622K05P096] using h

theorem momentScalarAmp2622K05P096_radius_le :
    (momentScalarAmp2622K05P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P096Expected]

def momentScalarGrow2622K05P096Input : RatPair2542 := (momentPanelGrowth2622K05P096 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P096Expected : RatState2542 :=
  ((((2260204954266660985062012717051038787466760927010629127993918421342096387215813928771953358467265 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1432575006230205948484797428595388259207107349783 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P096_replay :
    compactExp2620 momentScalarGrow2622K05P096Input 20 = momentScalarGrow2622K05P096Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P096_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P096Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P096]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P096 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P096 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P096Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P096_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P096] using h

theorem momentScalarGrow2622K05P096_radius_le :
    (momentScalarGrow2622K05P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P096Expected]

end ConnesWeilRH.Dev
