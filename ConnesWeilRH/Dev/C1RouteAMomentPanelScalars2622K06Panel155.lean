import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P155 : ℚ := ((-19002697 : ℚ) / 380650)

def momentPanelGrowth2622K06P155 : ℚ := ((63865921 : ℚ) / 49773025)

theorem momentPanelPhase_owner2622K06P155 :
    (momentPanelPhase2622K06P155 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P155 :
    (momentPanelGrowth2622K06P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P155Input : RatPair2542 := (momentPanelPhase2622K06P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P155Expected : RatState2542 :=
  ((((222765338730857713114364886878035266570926187853172503593205947087757229701 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((567221971490022544321558977 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P155_replay :
    compactExp2620 momentScalarAmp2622K06P155Input 20 = momentScalarAmp2622K06P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K06P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P155_replay] at h
  simpa only [momentPanelPhase_owner2622K06P155] using h

theorem momentScalarAmp2622K06P155_radius_le :
    (momentScalarAmp2622K06P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P155Expected]

def momentScalarGrow2622K06P155Input : RatPair2542 := (momentPanelGrowth2622K06P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P155Expected : RatState2542 :=
  ((((7706561435902640467723540313542391489329980984385879868110363644752438606233988024282128763876831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1221151909414278779389388967618883647954674412139 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P155_replay :
    compactExp2620 momentScalarGrow2622K06P155Input 20 = momentScalarGrow2622K06P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P155] using h

theorem momentScalarGrow2622K06P155_radius_le :
    (momentScalarGrow2622K06P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P155Expected]

end ConnesWeilRH.Dev
