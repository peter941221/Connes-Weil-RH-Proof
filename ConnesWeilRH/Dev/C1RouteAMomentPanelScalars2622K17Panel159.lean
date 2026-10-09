import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K17
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K17P159 : ℚ := ((-796247372714230181665279238661060096137 : ℚ) / 13980664939797096423226840311450828800)

def momentPanelGrowth2622K17P159 : ℚ := ((1433386379419074762300472836047894923 : ℚ) / 879242456318299912878113343248793600)

theorem momentPanelPhase_owner2622K17P159 :
    (momentPanelPhase2622K17P159 : ℝ) = momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (139 / 200) 0 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K17P159 :
    (momentPanelGrowth2622K17P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K17P159Input : RatPair2542 := (momentPanelPhase2622K17P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K17P159Expected : RatState2542 :=
  ((((196784612108799562653388028758273366212720372083266363945262640250143931 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2916787001510815972751413 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K17P159_replay :
    compactExp2620 momentScalarAmp2622K17P159Input 20 = momentScalarAmp2622K17P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K17P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K17P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K17P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K17P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K17P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K17P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K17P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K17P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K17P159_replay] at h
  simpa only [momentPanelPhase_owner2622K17P159] using h

theorem momentScalarAmp2622K17P159_radius_le :
    (momentScalarAmp2622K17P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarAmp2622K17P159Expected]

def momentScalarGrow2622K17P159Input : RatPair2542 := (momentPanelGrowth2622K17P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K17P159Expected : RatState2542 :=
  ((((10904552954112048245294132689465909684328945506340082149653113235475673613478748310514537265116207 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((13823141606244335237379389243470358042626457320773 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K17P159_replay :
    compactExp2620 momentScalarGrow2622K17P159Input 20 = momentScalarGrow2622K17P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K17P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K17P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K17P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K17P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K17P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K17P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K17P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K17P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K17P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K17P159] using h

theorem momentScalarGrow2622K17P159_radius_le :
    (momentScalarGrow2622K17P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarGrow2622K17P159Expected]

end ConnesWeilRH.Dev
