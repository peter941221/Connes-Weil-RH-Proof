import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P124 : ℚ := ((-85473310298421057855083564916047184270034459481046957 : ℚ) / 2514739072163266012430646963871537955549580414156800)

def momentPanelGrowth2622K01P124 : ℚ := ((402357896138611111615762929361283901752738571103291 : ℚ) / 1465319524908891360885515747684560419145756390195200)

theorem momentPanelPhase_owner2622K01P124 :
    (momentPanelPhase2622K01P124 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (69 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P124, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P124 :
    (momentPanelGrowth2622K01P124 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P124, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P124Input : RatPair2542 := (momentPanelPhase2622K01P124 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P124Expected : RatState2542 :=
  ((((1850803946646789747861243370624217328913504389883468949567192324852338519113270057 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2346248786040972686646898745808907 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P124_replay :
    compactExp2620 momentScalarAmp2622K01P124Input 20 = momentScalarAmp2622K01P124Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P124_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (69 / 200) 0) -
      (momentScalarAmp2622K01P124Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P124]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P124 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P124 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P124Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P124_replay] at h
  simpa only [momentPanelPhase_owner2622K01P124] using h

theorem momentScalarAmp2622K01P124_radius_le :
    (momentScalarAmp2622K01P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P124Expected]

def momentScalarGrow2622K01P124Input : RatPair2542 := (momentPanelGrowth2622K01P124 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P124Expected : RatState2542 :=
  ((((1405465845190228805143853293715875860700957384726109237666098363268708953626194747561119212479075 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3563278311407276297600909170340529843669806923369 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P124_replay :
    compactExp2620 momentScalarGrow2622K01P124Input 20 = momentScalarGrow2622K01P124Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P124_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P124Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P124]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P124 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P124 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P124Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P124_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P124] using h

theorem momentScalarGrow2622K01P124_radius_le :
    (momentScalarGrow2622K01P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P124Expected]

end ConnesWeilRH.Dev
