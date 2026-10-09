import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P102 : ℚ := ((-115759990986758962514696523829600910062908360512189 : ℚ) / 3836441797993620160284672685880242926596822925312)

def momentPanelGrowth2622K00P102 : ℚ := ((7717125981511206583116551196897532269065481717170076077 : ℚ) / 73568765701653983268274397906017955790875310099844300800)

theorem momentPanelPhase_owner2622K00P102 :
    (momentPanelPhase2622K00P102 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 8) 0 := by
  norm_num [momentPanelPhase2622K00P102, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P102 :
    (momentPanelGrowth2622K00P102 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P102, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P102Input : RatPair2542 := (momentPanelPhase2622K00P102 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P102Expected : RatState2542 :=
  ((((83995866551671454521746465640977622211986211264560100926725657451603423782932347021 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((53240237343439641662647190118758969 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P102_replay :
    compactExp2620 momentScalarAmp2622K00P102Input 20 = momentScalarAmp2622K00P102Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P102_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 8) 0) -
      (momentScalarAmp2622K00P102Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P102]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P102 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P102 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P102Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P102_replay] at h
  simpa only [momentPanelPhase_owner2622K00P102] using h

theorem momentScalarAmp2622K00P102_radius_le :
    (momentScalarAmp2622K00P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P102Expected]

def momentScalarGrow2622K00P102Input : RatPair2542 := (momentPanelGrowth2622K00P102 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P102Expected : RatState2542 :=
  ((((1186109285203291691392991715810785416625629763259450889358245344468738294064008882629238534043193 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1503571996910853406152020795339352892350059552213 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P102_replay :
    compactExp2620 momentScalarGrow2622K00P102Input 20 = momentScalarGrow2622K00P102Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P102_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P102Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P102]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P102 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P102 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P102Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P102_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P102] using h

theorem momentScalarGrow2622K00P102_radius_le :
    (momentScalarGrow2622K00P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P102Expected]

end ConnesWeilRH.Dev
