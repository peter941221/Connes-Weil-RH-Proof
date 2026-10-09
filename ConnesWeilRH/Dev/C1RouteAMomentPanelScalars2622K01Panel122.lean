import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P122 : ℚ := ((-227947628737255734015677688247196888576295914631127 : ℚ) / 6807971494207428632648024074274091800545701396480)

def momentPanelGrowth2622K01P122 : ℚ := ((711763435314513465599173125473026504472636614892852433 : ℚ) / 2833297938361043163612091302137875607237315104709017600)

theorem momentPanelPhase_owner2622K01P122 :
    (momentPanelPhase2622K01P122 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P122 :
    (momentPanelGrowth2622K01P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P122Input : RatPair2542 := (momentPanelPhase2622K01P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P122Expected : RatState2542 :=
  ((((383911656224400131899407650473041144612928772538606787333771918505400900426492421 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((7786902107993946212336387738527761 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P122_replay :
    compactExp2620 momentScalarAmp2622K01P122Input 20 = momentScalarAmp2622K01P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K01P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P122_replay] at h
  simpa only [momentPanelPhase_owner2622K01P122] using h

theorem momentScalarAmp2622K01P122_radius_le :
    (momentScalarAmp2622K01P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P122Expected]

def momentScalarGrow2622K01P122Input : RatPair2542 := (momentPanelGrowth2622K01P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P122Expected : RatState2542 :=
  ((((1372996302358789181856659978480315780666871470715395930647637255117673431118731578935838654962021 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3480958339637948229917270965473278503293267500361 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P122_replay :
    compactExp2620 momentScalarGrow2622K01P122Input 20 = momentScalarGrow2622K01P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P122] using h

theorem momentScalarGrow2622K01P122_radius_le :
    (momentScalarGrow2622K01P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P122Expected]

end ConnesWeilRH.Dev
