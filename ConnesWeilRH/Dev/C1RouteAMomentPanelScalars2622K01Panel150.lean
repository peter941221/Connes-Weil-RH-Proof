import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P150 : ℚ := ((-28476996895643628852224961412194669082555683599864051 : ℚ) / 603226237322173943729284564987829119392167860633600)

def momentPanelGrowth2622K01P150 : ℚ := ((436183713458925251656812755497228587669368923211003531 : ℚ) / 468920338335350283524857453033722106477495696175923200)

theorem momentPanelPhase_owner2622K01P150 :
    (momentPanelPhase2622K01P150 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P150 :
    (momentPanelGrowth2622K01P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P150Input : RatPair2542 := (momentPanelPhase2622K01P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P150Expected : RatState2542 :=
  ((((840256703960525707135990470440024289705572973061972607637772135360951708497 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((8524016813922254027816696333 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P150_replay :
    compactExp2620 momentScalarAmp2622K01P150Input 20 = momentScalarAmp2622K01P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K01P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P150_replay] at h
  simpa only [momentPanelPhase_owner2622K01P150] using h

theorem momentScalarAmp2622K01P150_radius_le :
    (momentScalarAmp2622K01P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P150Expected]

def momentScalarGrow2622K01P150Input : RatPair2542 := (momentPanelGrowth2622K01P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P150Expected : RatState2542 :=
  ((((2707346238356955963666504846448075163648430367945931997141129708379101627869593925762132985438173 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3431966039595248321719954064876446608741826098099 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P150_replay :
    compactExp2620 momentScalarGrow2622K01P150Input 20 = momentScalarGrow2622K01P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P150] using h

theorem momentScalarGrow2622K01P150_radius_le :
    (momentScalarGrow2622K01P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P150Expected]

end ConnesWeilRH.Dev
