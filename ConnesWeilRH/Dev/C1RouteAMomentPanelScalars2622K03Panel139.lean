import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P139 : ℚ := ((-218416809422850786168770327444350705253664608375289075 : ℚ) / 5516985993219492153354134782899878863823688358166528)

def momentPanelGrowth2622K03P139 : ℚ := ((734806924159535908826659701413194244339169597863 : ℚ) / 1370157784997721485815954530671515330927436759040)

theorem momentPanelPhase_owner2622K03P139 :
    (momentPanelPhase2622K03P139 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P139 :
    (momentPanelGrowth2622K03P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P139Input : RatPair2542 := (momentPanelPhase2622K03P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P139Expected : RatState2542 :=
  ((((6837581395832661375779466986132607690400882854823528827985780245253371341440261 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((17335985261354929595413597913641 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P139_replay :
    compactExp2620 momentScalarAmp2622K03P139Input 20 = momentScalarAmp2622K03P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K03P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P139_replay] at h
  simpa only [momentPanelPhase_owner2622K03P139] using h

theorem momentScalarAmp2622K03P139_radius_le :
    (momentScalarAmp2622K03P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P139Expected]

def momentScalarGrow2622K03P139Input : RatPair2542 := (momentPanelGrowth2622K03P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P139Expected : RatState2542 :=
  ((((1825904214852080819469063204254454531934010005350878210881533251727265195318461511183405579407377 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2314607390111437937348920556403169267686800208877 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P139_replay :
    compactExp2620 momentScalarGrow2622K03P139Input 20 = momentScalarGrow2622K03P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P139] using h

theorem momentScalarGrow2622K03P139_radius_le :
    (momentScalarGrow2622K03P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P139Expected]

end ConnesWeilRH.Dev
