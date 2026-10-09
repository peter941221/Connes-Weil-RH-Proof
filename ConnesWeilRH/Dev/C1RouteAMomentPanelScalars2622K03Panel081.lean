import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P081 : ℚ := ((-73135931290760367885992635558391048435751398704189325 : ℚ) / 2418237146668645241032772016333179791398197383921664)

def momentPanelGrowth2622K03P081 : ℚ := ((519861220640258058360554899703301133947431316840856425 : ℚ) / 8987007499553547321682803013675960937915162884462084096)

theorem momentPanelPhase_owner2622K03P081 :
    (momentPanelPhase2622K03P081 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P081 :
    (momentPanelGrowth2622K03P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P081Input : RatPair2542 := (momentPanelPhase2622K03P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P081Expected : RatState2542 :=
  ((((78340752246980495322207868613750214247372007434820701308434445155107814462948669401 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((99311565955977780351678605148028091 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P081_replay :
    compactExp2620 momentScalarAmp2622K03P081Input 20 = momentScalarAmp2622K03P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K03P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P081_replay] at h
  simpa only [momentPanelPhase_owner2622K03P081] using h

theorem momentScalarAmp2622K03P081_radius_le :
    (momentScalarAmp2622K03P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P081Expected]

def momentScalarGrow2622K03P081Input : RatPair2542 := (momentPanelGrowth2622K03P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P081Expected : RatState2542 :=
  ((((565797157164174608548060386742779626709358296179121734049313492183660000770476869685206743777443 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((179308266579907123170616668472870730482923477515 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K03P081_replay :
    compactExp2620 momentScalarGrow2622K03P081Input 20 = momentScalarGrow2622K03P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P081] using h

theorem momentScalarGrow2622K03P081_radius_le :
    (momentScalarGrow2622K03P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P081Expected]

end ConnesWeilRH.Dev
