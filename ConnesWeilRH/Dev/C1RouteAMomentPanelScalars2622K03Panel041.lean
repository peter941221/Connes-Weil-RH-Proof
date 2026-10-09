import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P041 : ℚ := ((-73342543896488370975708528302715361328106081211963325 : ℚ) / 1862866524482902132115371779900992243928943017590784)

def momentPanelGrowth2622K03P041 : ℚ := ((900374619633864997989847601969040998402709090396409475 : ℚ) / 1758210858517649170041480377748334425618977357574438912)

theorem momentPanelPhase_owner2622K03P041 :
    (momentPanelPhase2622K03P041 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-97 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P041 :
    (momentPanelGrowth2622K03P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P041Input : RatPair2542 := (momentPanelPhase2622K03P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P041Expected : RatState2542 :=
  ((((2128079161464854386166288347485101848124005841117353547675668449446058552791203 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((21582099354819499446831166005621 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P041_replay :
    compactExp2620 momentScalarAmp2622K03P041Input 20 = momentScalarAmp2622K03P041Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622K03P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P041]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P041 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P041_replay] at h
  simpa only [momentPanelPhase_owner2622K03P041] using h

theorem momentScalarAmp2622K03P041_radius_le :
    (momentScalarAmp2622K03P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P041Expected]

def momentScalarGrow2622K03P041Input : RatPair2542 := (momentPanelGrowth2622K03P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P041Expected : RatState2542 :=
  ((((1782253786930290678483921384992366392880484217660729432915944195959604873946297895457200192338935 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4518547958781378316497529743115906765341110555611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P041_replay :
    compactExp2620 momentScalarGrow2622K03P041Input 20 = momentScalarGrow2622K03P041Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P041_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P041] using h

theorem momentScalarGrow2622K03P041_radius_le :
    (momentScalarGrow2622K03P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P041Expected]

end ConnesWeilRH.Dev
