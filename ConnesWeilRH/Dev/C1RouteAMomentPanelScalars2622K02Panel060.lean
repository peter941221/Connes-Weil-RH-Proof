import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P060 : ℚ := ((-118370716994536840661444762177384545269143478758701553 : ℚ) / 3474777232661929926424503021221740859037434930790400)

def momentPanelGrowth2622K02P060 : ℚ := ((305226107545963426431477132605076699388648340879799 : ℚ) / 1181903814329805377504366611301126922438552479334400)

theorem momentPanelPhase_owner2622K02P060 :
    (momentPanelPhase2622K02P060 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-59 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P060, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P060 :
    (momentPanelGrowth2622K02P060 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P060, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P060Input : RatPair2542 := (momentPanelPhase2622K02P060 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P060Expected : RatState2542 :=
  ((((1714049292326705164670398210747707159163208866716111384913266070177306890059806981 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4345772412242395553002412388071067 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P060_replay :
    compactExp2620 momentScalarAmp2622K02P060Input 20 = momentScalarAmp2622K02P060Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P060_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-59 / 200) 0) -
      (momentScalarAmp2622K02P060Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P060]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P060 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P060 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P060Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P060_replay] at h
  simpa only [momentPanelPhase_owner2622K02P060] using h

theorem momentScalarAmp2622K02P060_radius_le :
    (momentScalarAmp2622K02P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P060Expected]

def momentScalarGrow2622K02P060Input : RatPair2542 := (momentPanelGrowth2622K02P060 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P060Expected : RatState2542 :=
  ((((1382690451537647067331976251559030537209762798400525229586882025817316294764711993983889554734547 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((438191987284843386650088130828333377821912902103 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P060_replay :
    compactExp2620 momentScalarGrow2622K02P060Input 20 = momentScalarGrow2622K02P060Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P060_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P060Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P060]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P060 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P060 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P060Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P060_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P060] using h

theorem momentScalarGrow2622K02P060_radius_le :
    (momentScalarGrow2622K02P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P060Expected]

end ConnesWeilRH.Dev
