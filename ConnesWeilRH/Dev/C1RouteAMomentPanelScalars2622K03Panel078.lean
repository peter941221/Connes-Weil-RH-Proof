import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P078 : ℚ := ((-73156910009189838537896020532333788519007943801977675 : ℚ) / 2403622130295336211850735168006016961201638058491904)

def momentPanelGrowth2622K03P078 : ℚ := ((41744584655650235149327071763527561571893050271825 : ℚ) / 541577700483432712626852960823427626471251502956544)

theorem momentPanelPhase_owner2622K03P078 :
    (momentPanelPhase2622K03P078 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P078 :
    (momentPanelGrowth2622K03P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P078Input : RatPair2542 := (momentPanelPhase2622K03P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P078Expected : RatState2542 :=
  ((((16153757488048951712043681603447513233487881183536272672488033620324427119104109089 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((81911659048437170753196767846834763 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P078_replay :
    compactExp2620 momentScalarAmp2622K03P078Input 20 = momentScalarAmp2622K03P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K03P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P078_replay] at h
  simpa only [momentPanelPhase_owner2622K03P078] using h

theorem momentScalarAmp2622K03P078_radius_le :
    (momentScalarAmp2622K03P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P078Expected]

def momentScalarGrow2622K03P078Input : RatPair2542 := (momentPanelGrowth2622K03P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P078Expected : RatState2542 :=
  ((((1153569740454168670474958560762007821145549759400874079310173853782022217463873856323438219925721 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((182790408299773322684380541094808127153582641787 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K03P078_replay :
    compactExp2620 momentScalarGrow2622K03P078Input 20 = momentScalarGrow2622K03P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P078] using h

theorem momentScalarGrow2622K03P078_radius_le :
    (momentScalarGrow2622K03P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P078Expected]

end ConnesWeilRH.Dev
