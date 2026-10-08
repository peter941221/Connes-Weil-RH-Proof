import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P075 : ℚ := ((-119296109070521746017899433408235643973082756899074999 : ℚ) / 3725972826578178865490761351844852003040798336614400)

def momentPanelGrowth2622K04P075 : ℚ := ((4121571250138217912624680983674032680708434631946287 : ℚ) / 21819905450857985257607181729540826594533068662374400)

theorem momentPanelPhase_owner2622K04P075 :
    (momentPanelPhase2622K04P075 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P075 :
    (momentPanelGrowth2622K04P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P075Input : RatPair2542 := (momentPanelPhase2622K04P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P075Expected : RatState2542 :=
  ((((3322854938488542973898960123086239321207490779094140663441044167690793275471083693 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((16849390705167158593674428389419673 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P075_replay :
    compactExp2620 momentScalarAmp2622K04P075Input 20 = momentScalarAmp2622K04P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K04P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P075_replay] at h
  simpa only [momentPanelPhase_owner2622K04P075] using h

theorem momentScalarAmp2622K04P075_radius_le :
    (momentScalarAmp2622K04P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P075Expected]

def momentScalarGrow2622K04P075Input : RatPair2542 := (momentPanelGrowth2622K04P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P075Expected : RatState2542 :=
  ((((322509636274158117521996777618055795753788230368669256596105042887340123604068869636414145765619 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1635317841423199673204814292513279399935872699289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P075_replay :
    compactExp2620 momentScalarGrow2622K04P075Input 20 = momentScalarGrow2622K04P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P075] using h

theorem momentScalarGrow2622K04P075_radius_le :
    (momentScalarGrow2622K04P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P075Expected]

end ConnesWeilRH.Dev
