import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P042 : ℚ := ((-2933612694599166062070916744041565641881669253306875 : ℚ) / 75450022027207863152265229488978110889737517531136)

def momentPanelGrowth2622K03P042 : ℚ := ((10338745029030702635138555772544502029238876545696425 : ℚ) / 21133405019657189378657670411379497231913513067216896)

theorem momentPanelPhase_owner2622K03P042 :
    (momentPanelPhase2622K03P042 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P042 :
    (momentPanelGrowth2622K03P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P042Input : RatPair2542 := (momentPanelPhase2622K03P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P042Expected : RatState2542 :=
  ((((13884568564706178663093764891222311479353541939408686609955485362528765057103471 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((35202871077261405144838022528171 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P042_replay :
    compactExp2620 momentScalarAmp2622K03P042Input 20 = momentScalarAmp2622K03P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K03P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P042_replay] at h
  simpa only [momentPanelPhase_owner2622K03P042] using h

theorem momentScalarAmp2622K03P042_radius_le :
    (momentScalarAmp2622K03P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P042Expected]

def momentScalarGrow2622K03P042Input : RatPair2542 := (momentPanelGrowth2622K03P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P042Expected : RatState2542 :=
  ((((1741932407825912007491961251238768127515276271133155448101417665744163454995266551957093921238095 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4416321264238731631639214372845140626737651723625 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P042_replay :
    compactExp2620 momentScalarGrow2622K03P042Input 20 = momentScalarGrow2622K03P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P042] using h

theorem momentScalarGrow2622K03P042_radius_le :
    (momentScalarGrow2622K03P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P042Expected]

end ConnesWeilRH.Dev
