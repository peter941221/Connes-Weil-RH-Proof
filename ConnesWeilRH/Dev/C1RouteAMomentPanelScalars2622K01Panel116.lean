import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P116 : ℚ := ((-28501299238902392418735163107605605588872324531671807 : ℚ) / 884679482323789232273978558163269560286845494886400)

def momentPanelGrowth2622K01P116 : ℚ := ((583746035400816162127511083533711649777844776584099393 : ℚ) / 3066849896300061026628707101606652092364714996767129600)

theorem momentPanelPhase_owner2622K01P116 :
    (momentPanelPhase2622K01P116 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P116 :
    (momentPanelGrowth2622K01P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P116Input : RatPair2542 := (momentPanelPhase2622K01P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P116Expected : RatState2542 :=
  ((((10892041782944457682047021912608720814918440105912331640973950734867020063347250223 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((13807727528182081674519556127304513 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P116_replay :
    compactExp2620 momentScalarAmp2622K01P116Input 20 = momentScalarAmp2622K01P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K01P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P116_replay] at h
  simpa only [momentPanelPhase_owner2622K01P116] using h

theorem momentScalarAmp2622K01P116_radius_le :
    (momentScalarAmp2622K01P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P116Expected]

def momentScalarGrow2622K01P116Input : RatPair2542 := (momentPanelGrowth2622K01P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P116Expected : RatState2542 :=
  ((((1291910675859490455638624110000491262324946646547350857539419208536495991464299156309428472998259 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1637691046416024596178904012184708833627713618085 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P116_replay :
    compactExp2620 momentScalarGrow2622K01P116Input 20 = momentScalarGrow2622K01P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P116] using h

theorem momentScalarGrow2622K01P116_radius_le :
    (momentScalarGrow2622K01P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P116Expected]

end ConnesWeilRH.Dev
