import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P031 : ℚ := ((-360502536188931857353670834949525265313458711369123773 : ℚ) / 7510462808557302086104912428437133306673289284812800)

def momentPanelGrowth2622K02P031 : ℚ := ((1766812873979758414220376611050810211600221328807268373 : ℚ) / 2021808681111408130561701362831005535953393915055308800)

theorem momentPanelPhase_owner2622K02P031 :
    (momentPanelPhase2622K02P031 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P031 :
    (momentPanelGrowth2622K02P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P031Input : RatPair2542 := (momentPanelPhase2622K02P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P031Expected : RatState2542 :=
  ((((1522000873476477178688546574639921453707881685006870620061580361130980994783 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3861325136131307753237990257 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P031_replay :
    compactExp2620 momentScalarAmp2622K02P031Input 20 = momentScalarAmp2622K02P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K02P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P031_replay] at h
  simpa only [momentPanelPhase_owner2622K02P031] using h

theorem momentScalarAmp2622K02P031_radius_le :
    (momentScalarAmp2622K02P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P031Expected]

def momentScalarGrow2622K02P031Input : RatPair2542 := (momentPanelGrowth2622K02P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P031Expected : RatState2542 :=
  ((((2559108745598512575527864655776569517635306939770031920375234591591512575869474285281152778513051 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6488106067660927979047756911340587677013749598075 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P031_replay :
    compactExp2620 momentScalarGrow2622K02P031Input 20 = momentScalarGrow2622K02P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P031] using h

theorem momentScalarGrow2622K02P031_radius_le :
    (momentScalarGrow2622K02P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P031Expected]

end ConnesWeilRH.Dev
