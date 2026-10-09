import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P089 : ℚ := ((-1827613625073922792586240785550040783437394093811947843 : ℚ) / 60894379157915401901280405858144379690851714360934400)

def momentPanelGrowth2622K00P089 : ℚ := ((2297843044705158407244449210425138507581597606931192157 : ℚ) / 76104653730127766194222566551384796365355810053475532800)

theorem momentPanelPhase_owner2622K00P089 :
    (momentPanelPhase2622K00P089 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P089 :
    (momentPanelGrowth2622K00P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P089Input : RatPair2542 := (momentPanelPhase2622K00P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P089Expected : RatState2542 :=
  ((((98663201721753986502758424181425079942571203772291009620500404501313913821860949683 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((125074046762449770201439933324590883 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P089_replay :
    compactExp2620 momentScalarAmp2622K00P089Input 20 = momentScalarAmp2622K00P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K00P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P089_replay] at h
  simpa only [momentPanelPhase_owner2622K00P089] using h

theorem momentScalarAmp2622K00P089_radius_le :
    (momentScalarAmp2622K00P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P089Expected]

def momentScalarGrow2622K00P089Input : RatPair2542 := (momentPanelGrowth2622K00P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P089Expected : RatState2542 :=
  ((((1100731403778888146086469116407509411987197376556389640899551761524468116095834869614295207980933 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((43604462016006227514097101089620148684304921919 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K00P089_replay :
    compactExp2620 momentScalarGrow2622K00P089Input 20 = momentScalarGrow2622K00P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P089] using h

theorem momentScalarGrow2622K00P089_radius_le :
    (momentScalarGrow2622K00P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P089Expected]

end ConnesWeilRH.Dev
