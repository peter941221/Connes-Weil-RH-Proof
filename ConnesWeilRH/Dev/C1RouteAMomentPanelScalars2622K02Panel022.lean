import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P022 : ℚ := ((-2877542626277598673271380106100391953668240696957043 : ℚ) / 49725309613875642256070683175620410551574892380160)

def momentPanelGrowth2622K02P022 : ℚ := ((30475955729086483525668439288331535447729422518813 : ℚ) / 20980541082777610251556803750907578504826375372800)

theorem momentPanelPhase_owner2622K02P022 :
    (momentPanelPhase2622K02P022 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P022 :
    (momentPanelGrowth2622K02P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P022Input : RatPair2542 := (momentPanelPhase2622K02P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P022Expected : RatState2542 :=
  ((((78791628002007463722764455561555361658323489101192121058524187833075961 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2617623172969573678790663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P022_replay :
    compactExp2620 momentScalarAmp2622K02P022Input 20 = momentScalarAmp2622K02P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K02P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P022_replay] at h
  simpa only [momentPanelPhase_owner2622K02P022] using h

theorem momentScalarAmp2622K02P022_radius_le :
    (momentScalarAmp2622K02P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P022Expected]

def momentScalarGrow2622K02P022Input : RatPair2542 := (momentPanelGrowth2622K02P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P022Expected : RatState2542 :=
  ((((4564749519131281614587990459027722754321533215442901520627204131544720823080828569784316786466901 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1446624862958056527577012758603909357263796763329 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P022_replay :
    compactExp2620 momentScalarGrow2622K02P022Input 20 = momentScalarGrow2622K02P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P022] using h

theorem momentScalarGrow2622K02P022_radius_le :
    (momentScalarGrow2622K02P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P022Expected]

end ConnesWeilRH.Dev
