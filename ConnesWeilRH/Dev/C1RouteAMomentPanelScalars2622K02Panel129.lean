import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P129 : ℚ := ((-108992373604889226138302013259250322194997420601278827 : ℚ) / 3212163657204033308309778402843033753943009551974400)

def momentPanelGrowth2622K02P129 : ℚ := ((7994016975817799071107743304717906004512915638813 : ℚ) / 20980541082777610251556803750907578504826375372800)

theorem momentPanelPhase_owner2622K02P129 :
    (momentPanelPhase2622K02P129 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P129 :
    (momentPanelGrowth2622K02P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P129Input : RatPair2542 := (momentPanelPhase2622K02P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P129Expected : RatState2542 :=
  ((((1960929164263811678308517508976412679413194409912167443847050934290073588537986713 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4971706944722717201126357398072989 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P129_replay :
    compactExp2620 momentScalarAmp2622K02P129Input 20 = momentScalarAmp2622K02P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K02P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P129_replay] at h
  simpa only [momentPanelPhase_owner2622K02P129] using h

theorem momentScalarAmp2622K02P129_radius_le :
    (momentScalarAmp2622K02P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P129Expected]

def momentScalarGrow2622K02P129Input : RatPair2542 := (momentPanelGrowth2622K02P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P129Expected : RatState2542 :=
  ((((1563305055743504459457838849641010865285734229424324652506930529337467118304196364847924644158549 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1981723872154940249770820320137653050967778883081 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P129_replay :
    compactExp2620 momentScalarGrow2622K02P129Input 20 = momentScalarGrow2622K02P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P129] using h

theorem momentScalarGrow2622K02P129_radius_le :
    (momentScalarGrow2622K02P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P129Expected]

end ConnesWeilRH.Dev
