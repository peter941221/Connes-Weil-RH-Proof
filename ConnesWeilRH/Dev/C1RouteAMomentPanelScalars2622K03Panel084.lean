import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P084 : ℚ := ((-73114621594122579942991705493987816049358739414968775 : ℚ) / 2428467658129961561460197810162193772535788911722496)

def momentPanelGrowth2622K03P084 : ℚ := ((22230264317321757712767248891185508424812354560687425 : ℚ) / 566796002579429775661889930342249134743103347481378816)

theorem momentPanelPhase_owner2622K03P084 :
    (momentPanelPhase2622K03P084 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P084 :
    (momentPanelGrowth2622K03P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P084Input : RatPair2542 := (momentPanelPhase2622K03P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P084Expected : RatState2542 :=
  ((((89770009932817416792462840265592011886806437043800882832768134498444298775929709699 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((113800274425966958906497668487108739 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P084_replay :
    compactExp2620 momentScalarAmp2622K03P084Input 20 = momentScalarAmp2622K03P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K03P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P084_replay] at h
  simpa only [momentPanelPhase_owner2622K03P084] using h

theorem momentScalarAmp2622K03P084_radius_le :
    (momentScalarAmp2622K03P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P084Expected]

def momentScalarGrow2622K03P084Input : RatPair2542 := (momentPanelGrowth2622K03P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P084Expected : RatState2542 :=
  ((((1110713495566876248666503158362736404206216708671760881613696654343139165513758054020405924783945 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2815993153344508755705762890394877998168703867617 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P084_replay :
    compactExp2620 momentScalarGrow2622K03P084Input 20 = momentScalarGrow2622K03P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P084] using h

theorem momentScalarGrow2622K03P084_radius_le :
    (momentScalarGrow2622K03P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P084Expected]

end ConnesWeilRH.Dev
