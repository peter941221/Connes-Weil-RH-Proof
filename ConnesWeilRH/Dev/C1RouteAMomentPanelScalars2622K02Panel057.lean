import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P057 : ℚ := ((-949622772003228513861840161602602999056641722347479 : ℚ) / 27231885976829714530592096297096367202182805585920)

def momentPanelGrowth2622K02P057 : ℚ := ((3289302083137653834643954429817033363454948531529837359 : ℚ) / 11333191753444172654448365208551502428949260418836070400)

theorem momentPanelPhase_owner2622K02P057 :
    (momentPanelPhase2622K02P057 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P057, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P057 :
    (momentPanelGrowth2622K02P057 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P057, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P057Input : RatPair2542 := (momentPanelPhase2622K02P057 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P057Expected : RatState2542 :=
  ((((382773574599283837525310640280581143237477116101205227772006006722729113261866621 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((970478578350700123843360445054809 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P057_replay :
    compactExp2620 momentScalarAmp2622K02P057Input 20 = momentScalarAmp2622K02P057Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P057_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 40) 0) -
      (momentScalarAmp2622K02P057Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P057]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P057 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P057 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P057Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P057_replay] at h
  simpa only [momentPanelPhase_owner2622K02P057] using h

theorem momentScalarAmp2622K02P057_radius_le :
    (momentScalarAmp2622K02P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P057Expected]

def momentScalarGrow2622K02P057Input : RatPair2542 := (momentPanelGrowth2622K02P057 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P057Expected : RatState2542 :=
  ((((1427633007974693314169191471096612734818262323438871208303421090035704527626286654499713669318087 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((452434834636382830866188972520657418238191839615 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P057_replay :
    compactExp2620 momentScalarGrow2622K02P057Input 20 = momentScalarGrow2622K02P057Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P057_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P057Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P057]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P057 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P057 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P057Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P057_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P057] using h

theorem momentScalarGrow2622K02P057_radius_le :
    (momentScalarGrow2622K02P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P057Expected]

end ConnesWeilRH.Dev
