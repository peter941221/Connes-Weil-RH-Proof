import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P084 : ℚ := ((-115033059956628410723674161928011983244370888188356417 : ℚ) / 3794480715828064939781559078378427769587170174566400)

def momentPanelGrowth2622K02P084 : ℚ := ((68321135322663235108594809312573336191632602189786999 : ℚ) / 885618754030359024471703016159764273036098980439654400)

theorem momentPanelPhase_owner2622K02P084 :
    (momentPanelPhase2622K02P084 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P084 :
    (momentPanelGrowth2622K02P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P084Input : RatPair2542 := (momentPanelPhase2622K02P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P084Expected : RatState2542 :=
  ((((9108668410866942332395396743560989681453017676029395692729357251113080999249141903 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((11546942812912254771311388456103569 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K02P084_replay :
    compactExp2620 momentScalarAmp2622K02P084Input 20 = momentScalarAmp2622K02P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K02P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P084_replay] at h
  simpa only [momentPanelPhase_owner2622K02P084] using h

theorem momentScalarAmp2622K02P084_radius_le :
    (momentScalarAmp2622K02P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P084Expected]

def momentScalarGrow2622K02P084Input : RatPair2542 := (momentPanelGrowth2622K02P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P084Expected : RatState2542 :=
  ((((1153645302847401307476050260313668092634731650847013009836635239904565023061157549449183370439591 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1462419053012929133961137578364505135753168049405 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P084_replay :
    compactExp2620 momentScalarGrow2622K02P084Input 20 = momentScalarGrow2622K02P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P084] using h

theorem momentScalarGrow2622K02P084_radius_le :
    (momentScalarGrow2622K02P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P084Expected]

end ConnesWeilRH.Dev
