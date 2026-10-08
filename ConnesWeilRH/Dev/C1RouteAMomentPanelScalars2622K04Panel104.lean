import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P104 : ℚ := ((-109063521762431834951426321703683577848156702940925001 : ℚ) / 3725972826578178865490761351844852003040798336614400)

def momentPanelGrowth2622K04P104 : ℚ := ((4121571250138217912624680983674032680708434631946287 : ℚ) / 21819905450857985257607181729540826594533068662374400)

theorem momentPanelPhase_owner2622K04P104 :
    (momentPanelPhase2622K04P104 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P104 :
    (momentPanelGrowth2622K04P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P104Input : RatPair2542 := (momentPanelPhase2622K04P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P104Expected : RatState2542 :=
  ((((51785511772897665377078407005010355059816270877508835729901972904488372818582108327 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((262591070495417384790983222159866213 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P104_replay :
    compactExp2620 momentScalarAmp2622K04P104Input 20 = momentScalarAmp2622K04P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K04P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P104_replay] at h
  simpa only [momentPanelPhase_owner2622K04P104] using h

theorem momentScalarAmp2622K04P104_radius_le :
    (momentScalarAmp2622K04P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P104Expected]

def momentScalarGrow2622K04P104Input : RatPair2542 := (momentPanelGrowth2622K04P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P104Expected : RatState2542 :=
  ((((322509636274158117521996777618055795753788230368669256596105042887340123604068869636414145765619 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1635317841423199673204814292513279399935872699289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P104_replay :
    compactExp2620 momentScalarGrow2622K04P104Input 20 = momentScalarGrow2622K04P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P104] using h

theorem momentScalarGrow2622K04P104_radius_le :
    (momentScalarGrow2622K04P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P104Expected]

end ConnesWeilRH.Dev
