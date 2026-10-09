import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P095 : ℚ := ((-113326570876325170245651593183907238576868571651643583 : ℚ) / 3794480715828064939781559078378427769587170174566400)

def momentPanelGrowth2622K02P095 : ℚ := ((68321135322663235108594809312573336191632602189786999 : ℚ) / 885618754030359024471703016159764273036098980439654400)

theorem momentPanelPhase_owner2622K02P095 :
    (momentPanelPhase2622K02P095 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P095, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P095 :
    (momentPanelGrowth2622K02P095 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P095, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P095Input : RatPair2542 := (momentPanelPhase2622K02P095 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P095Expected : RatState2542 :=
  ((((14281368886783843186219610729880296823160523052725067394281915286650476485959332589 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((144834411932989781467063512527759943 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P095_replay :
    compactExp2620 momentScalarAmp2622K02P095Input 20 = momentScalarAmp2622K02P095Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P095_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 200) 0) -
      (momentScalarAmp2622K02P095Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P095]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P095 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P095 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P095Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P095_replay] at h
  simpa only [momentPanelPhase_owner2622K02P095] using h

theorem momentScalarAmp2622K02P095_radius_le :
    (momentScalarAmp2622K02P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P095Expected]

def momentScalarGrow2622K02P095Input : RatPair2542 := (momentPanelGrowth2622K02P095 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P095Expected : RatState2542 :=
  ((((1153645302847401307476050260313668092634731650847013009836635239904565023061157549449183370439591 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1462419053012929133961137578364505135753168049405 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P095_replay :
    compactExp2620 momentScalarGrow2622K02P095Input 20 = momentScalarGrow2622K02P095Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P095_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P095Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P095]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P095 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P095 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P095Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P095_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P095] using h

theorem momentScalarGrow2622K02P095_radius_le :
    (momentScalarGrow2622K02P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P095Expected]

end ConnesWeilRH.Dev
