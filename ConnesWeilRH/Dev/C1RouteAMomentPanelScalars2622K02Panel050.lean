import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P050 : ℚ := ((-119367257228064354831023741852668899626242039238721173 : ℚ) / 3212163657204033308309778402843033753943009551974400)

def momentPanelGrowth2622K02P050 : ℚ := ((7994016975817799071107743304717906004512915638813 : ℚ) / 20980541082777610251556803750907578504826375372800)

theorem momentPanelPhase_owner2622K02P050 :
    (momentPanelPhase2622K02P050 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-79 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P050, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P050 :
    (momentPanelGrowth2622K02P050 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P050, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P050Input : RatPair2542 := (momentPanelPhase2622K02P050 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P050Expected : RatState2542 :=
  ((((155158467225390036575714736433092139379684334652691587909406371124185320073547897 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((98346848565056139914675554047245 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P050_replay :
    compactExp2620 momentScalarAmp2622K02P050Input 20 = momentScalarAmp2622K02P050Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P050_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-79 / 200) 0) -
      (momentScalarAmp2622K02P050Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P050]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P050 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P050 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P050Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P050_replay] at h
  simpa only [momentPanelPhase_owner2622K02P050] using h

theorem momentScalarAmp2622K02P050_radius_le :
    (momentScalarAmp2622K02P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P050Expected]

def momentScalarGrow2622K02P050Input : RatPair2542 := (momentPanelGrowth2622K02P050 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P050Expected : RatState2542 :=
  ((((1563305055743504459457838849641010865285734229424324652506930529337467118304196364847924644158549 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1981723872154940249770820320137653050967778883081 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P050_replay :
    compactExp2620 momentScalarGrow2622K02P050Input 20 = momentScalarGrow2622K02P050Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P050_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P050Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P050]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P050 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P050 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P050Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P050_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P050] using h

theorem momentScalarGrow2622K02P050_radius_le :
    (momentScalarGrow2622K02P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P050Expected]

end ConnesWeilRH.Dev
