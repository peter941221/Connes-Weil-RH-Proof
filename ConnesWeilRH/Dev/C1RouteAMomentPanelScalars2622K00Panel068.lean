import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P068 : ℚ := ((-1857086595053305203100564118917340705194087973263233401 : ℚ) / 58080988506053413783738312555165534878014044215705600)

def momentPanelGrowth2622K00P068 : ℚ := ((732210824602006736001806677383984454016868842803375637 : ℚ) / 4308111764690160793169385953291258721691938392427724800)

theorem momentPanelPhase_owner2622K00P068 :
    (momentPanelPhase2622K00P068 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-43 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P068 :
    (momentPanelGrowth2622K00P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P068Input : RatPair2542 := (momentPanelPhase2622K00P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P068Expected : RatState2542 :=
  ((((433759474896603553477896240657328175955461909748401680490185463643511589396608033 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((8797955610711931970565160166339553 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P068_replay :
    compactExp2620 momentScalarAmp2622K00P068Input 20 = momentScalarAmp2622K00P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K00P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P068_replay] at h
  simpa only [momentPanelPhase_owner2622K00P068] using h

theorem momentScalarAmp2622K00P068_radius_le :
    (momentScalarAmp2622K00P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P068Expected]

def momentScalarGrow2622K00P068Input : RatPair2542 := (momentPanelGrowth2622K00P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P068Expected : RatState2542 :=
  ((((1265848482232364039786834883289242872805112724481031141888665900192634488397734847833408667432447 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1604653328205734055759121459170189675972938329883 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P068_replay :
    compactExp2620 momentScalarGrow2622K00P068Input 20 = momentScalarGrow2622K00P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P068] using h

theorem momentScalarGrow2622K00P068_radius_le :
    (momentScalarGrow2622K00P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P068Expected]

end ConnesWeilRH.Dev
