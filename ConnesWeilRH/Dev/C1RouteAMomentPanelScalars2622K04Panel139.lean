import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P139 : ℚ := ((-302130745768917614173530277822499098854117319817649573 : ℚ) / 8620290614405456489615835598281060724724513059635200)

def momentPanelGrowth2622K04P139 : ℚ := ((268907532259062169032605348802438508409839995421 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K04P139 :
    (momentPanelPhase2622K04P139 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P139 :
    (momentPanelGrowth2622K04P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P139Input : RatPair2542 := (momentPanelPhase2622K04P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P139Expected : RatState2542 :=
  ((((1282634766433061398633441833145826075572252749628305510824302975025513170410136751 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((203248385235144139734741054127147 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P139_replay :
    compactExp2620 momentScalarAmp2622K04P139Input 20 = momentScalarAmp2622K04P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K04P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P139_replay] at h
  simpa only [momentPanelPhase_owner2622K04P139] using h

theorem momentScalarAmp2622K04P139_radius_le :
    (momentScalarAmp2622K04P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P139Expected]

def momentScalarGrow2622K04P139Input : RatPair2542 := (momentPanelGrowth2622K04P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P139Expected : RatState2542 :=
  ((((2001335133382166530590255564803516196247227254512063604311815404808693219417238476593105256493337 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2536992163586244601090499810136575478165836427611 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P139_replay :
    compactExp2620 momentScalarGrow2622K04P139Input 20 = momentScalarGrow2622K04P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P139] using h

theorem momentScalarGrow2622K04P139_radius_le :
    (momentScalarGrow2622K04P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P139Expected]

end ConnesWeilRH.Dev
