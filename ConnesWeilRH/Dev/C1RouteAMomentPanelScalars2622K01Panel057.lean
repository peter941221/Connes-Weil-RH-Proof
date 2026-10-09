import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P057 : ℚ := ((-228771632928651427922973821976641555066183005048873 : ℚ) / 6807971494207428632648024074274091800545701396480)

def momentPanelGrowth2622K01P057 : ℚ := ((711763435314513465599173125473026504472636614892852433 : ℚ) / 2833297938361043163612091302137875607237315104709017600)

theorem momentPanelPhase_owner2622K01P057 :
    (momentPanelPhase2622K01P057 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P057, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P057 :
    (momentPanelGrowth2622K01P057 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P057, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P057Input : RatPair2542 := (momentPanelPhase2622K01P057 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P057Expected : RatState2542 :=
  ((((2721174332164579259333583443104123887734668842972893457083640812299023829977621869 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6899217647640170631179875186165365 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P057_replay :
    compactExp2620 momentScalarAmp2622K01P057Input 20 = momentScalarAmp2622K01P057Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P057_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 40) 0) -
      (momentScalarAmp2622K01P057Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P057]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P057 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P057 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P057Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P057_replay] at h
  simpa only [momentPanelPhase_owner2622K01P057] using h

theorem momentScalarAmp2622K01P057_radius_le :
    (momentScalarAmp2622K01P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P057Expected]

def momentScalarGrow2622K01P057Input : RatPair2542 := (momentPanelGrowth2622K01P057 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P057Expected : RatState2542 :=
  ((((1372996302358789181856659978480315780666871470715395930647637255117673431118731578935838654962021 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3480958339637948229917270965473278503293267500361 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P057_replay :
    compactExp2620 momentScalarGrow2622K01P057Input 20 = momentScalarGrow2622K01P057Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P057_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P057Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P057]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P057 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P057 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P057Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P057_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P057] using h

theorem momentScalarGrow2622K01P057_radius_le :
    (momentScalarGrow2622K01P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P057Expected]

end ConnesWeilRH.Dev
