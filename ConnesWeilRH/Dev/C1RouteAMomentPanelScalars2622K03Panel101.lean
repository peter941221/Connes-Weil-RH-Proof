import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P101 : ℚ := ((-72993253723900453282472462739294513446585310495622325 : ℚ) / 2403622130295336211850735168006016961201638058491904)

def momentPanelGrowth2622K03P101 : ℚ := ((41744584655650235149327071763527561571893050271825 : ℚ) / 541577700483432712626852960823427626471251502956544)

theorem momentPanelPhase_owner2622K03P101 :
    (momentPanelPhase2622K03P101 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P101 :
    (momentPanelGrowth2622K03P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P101Input : RatPair2542 := (momentPanelPhase2622K03P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P101Expected : RatState2542 :=
  ((((138335457391995575039345699215465502088501472806417067554367462586522904172518184865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((21920763042280307138876981352964679 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P101_replay :
    compactExp2620 momentScalarAmp2622K03P101Input 20 = momentScalarAmp2622K03P101Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622K03P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P101]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P101 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P101_replay] at h
  simpa only [momentPanelPhase_owner2622K03P101] using h

theorem momentScalarAmp2622K03P101_radius_le :
    (momentScalarAmp2622K03P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P101Expected]

def momentScalarGrow2622K03P101Input : RatPair2542 := (momentPanelGrowth2622K03P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P101Expected : RatState2542 :=
  ((((1153569740454168670474958560762007821145549759400874079310173853782022217463873856323438219925721 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((182790408299773322684380541094808127153582641787 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K03P101_replay :
    compactExp2620 momentScalarGrow2622K03P101Input 20 = momentScalarGrow2622K03P101Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P101_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P101] using h

theorem momentScalarGrow2622K03P101_radius_le :
    (momentScalarGrow2622K03P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P101Expected]

end ConnesWeilRH.Dev
