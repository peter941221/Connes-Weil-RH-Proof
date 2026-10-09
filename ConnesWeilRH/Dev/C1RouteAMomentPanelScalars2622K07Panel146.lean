import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P146 : ℚ := ((-29092642287322101440810785398002966425 : ℚ) / 736413727889384849752676799692668928)

def momentPanelGrowth2622K07P146 : ℚ := ((1536580099879521398943930191771210106075 : ℚ) / 1848782240756876269786980697117433004032)

theorem momentPanelPhase_owner2622K07P146 :
    (momentPanelPhase2622K07P146 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P146 :
    (momentPanelGrowth2622K07P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P146Input : RatPair2542 := (momentPanelPhase2622K07P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P146Expected : RatState2542 :=
  ((((7437049425982518552954839815383491042848565771910636065558926744229311464078203 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2356984143778000477286512774455 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P146_replay :
    compactExp2620 momentScalarAmp2622K07P146Input 20 = momentScalarAmp2622K07P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K07P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P146_replay] at h
  simpa only [momentPanelPhase_owner2622K07P146] using h

theorem momentScalarAmp2622K07P146_radius_le :
    (momentScalarAmp2622K07P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P146Expected]

def momentScalarGrow2622K07P146Input : RatPair2542 := (momentPanelGrowth2622K07P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P146Expected : RatState2542 :=
  ((((4904042083185939470902539083966726933505280590914869463173349569927744712271200289409255180029473 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3108303481417544796172220806977823291555921407613 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P146_replay :
    compactExp2620 momentScalarGrow2622K07P146Input 20 = momentScalarGrow2622K07P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P146] using h

theorem momentScalarGrow2622K07P146_radius_le :
    (momentScalarGrow2622K07P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P146Expected]

end ConnesWeilRH.Dev
