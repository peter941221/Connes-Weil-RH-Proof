import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P038 : ℚ := ((-127818656215801237563783833714879543384945564269988957 : ℚ) / 2796549129088057790945605528539340770228353735065600)

def momentPanelGrowth2622K04P038 : ℚ := ((105234569783855856803332788804911431076530233344741 : ℚ) / 154570925120055455118612370491380323270251459379200)

theorem momentPanelPhase_owner2622K04P038 :
    (momentPanelPhase2622K04P038 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-103 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P038 :
    (momentPanelGrowth2622K04P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P038Input : RatPair2542 := (momentPanelPhase2622K04P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P038Expected : RatState2542 :=
  ((((30185611609365303245519028701358373246002600048007898919654688323969657818009 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((38268894468306265440137231089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P038_replay :
    compactExp2620 momentScalarAmp2622K04P038Input 20 = momentScalarAmp2622K04P038Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622K04P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P038]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P038 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P038_replay] at h
  simpa only [momentPanelPhase_owner2622K04P038] using h

theorem momentScalarAmp2622K04P038_radius_le :
    (momentScalarAmp2622K04P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P038Expected]

def momentScalarGrow2622K04P038Input : RatPair2542 := (momentPanelGrowth2622K04P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P038Expected : RatState2542 :=
  ((((2109812403298710555571336071790076207266174732575588584227557306061929608305764281813885293768657 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2674503222913815012743155906118655515653701629345 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P038_replay :
    compactExp2620 momentScalarGrow2622K04P038Input 20 = momentScalarGrow2622K04P038Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P038_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P038] using h

theorem momentScalarGrow2622K04P038_radius_le :
    (momentScalarGrow2622K04P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P038Expected]

end ConnesWeilRH.Dev
