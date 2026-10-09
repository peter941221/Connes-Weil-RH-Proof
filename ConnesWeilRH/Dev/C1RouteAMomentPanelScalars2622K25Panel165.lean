import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P165 : ℚ := ((-797699362703871122702313070268556267973 : ℚ) / 11627905425773502654048959162272972800)

def momentPanelGrowth2622K25P165 : ℚ := ((946535961229824641267708094562628947 : ℚ) / 368125734306277818194642610841190400)

theorem momentPanelPhase_owner2622K25P165 :
    (momentPanelPhase2622K25P165 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (151 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P165, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P165 :
    (momentPanelGrowth2622K25P165 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P165, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P165Input : RatPair2542 := (momentPanelPhase2622K25P165 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P165Expected : RatState2542 :=
  ((((1718033148316421102036256847790977382654886711357731482488168177363 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208927997622873511984869 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K25P165_replay :
    compactExp2620 momentScalarAmp2622K25P165Input 20 = momentScalarAmp2622K25P165Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P165_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (151 / 200) 0) -
      (momentScalarAmp2622K25P165Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P165]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P165 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P165 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P165Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P165_replay] at h
  simpa only [momentPanelPhase_owner2622K25P165] using h

theorem momentScalarAmp2622K25P165_radius_le :
    (momentScalarAmp2622K25P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P165Expected]

def momentScalarGrow2622K25P165Input : RatPair2542 := (momentPanelGrowth2622K25P165 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P165Expected : RatState2542 :=
  ((((27942782342681530346951419293675736686255609165839057248078353636614798622401322162435252294305865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4427699743846286885347613671761736936420704624175 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K25P165_replay :
    compactExp2620 momentScalarGrow2622K25P165Input 20 = momentScalarGrow2622K25P165Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P165_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P165Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P165]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P165 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P165 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P165Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P165_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P165] using h

theorem momentScalarGrow2622K25P165_radius_le :
    (momentScalarGrow2622K25P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P165Expected]

end ConnesWeilRH.Dev
