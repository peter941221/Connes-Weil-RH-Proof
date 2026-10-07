import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P090 : ℚ := ((-1826140468253334502922971296240666765702437263628052157 : ℚ) / 60894379157915401901280405858144379690851714360934400)

def momentPanelGrowth2622P090 : ℚ := ((2297843044705158407244449210425138507581597606931192157 : ℚ) / 76104653730127766194222566551384796365355810053475532800)

theorem momentPanelPhase_owner2622P090 :
    (momentPanelPhase2622P090 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 200) 0 := by
  norm_num [momentPanelPhase2622P090, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P090 :
    (momentPanelGrowth2622P090 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P090, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P090Input : RatPair2542 := (momentPanelPhase2622P090 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P090Expected : RatState2542 :=
  ((((101079167592887758577970617246212921990812113026980070021664064665815804861478277365 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((256273464106647231434436450569067779 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P090_replay :
    compactExp2620 momentScalarAmp2622P090Input 20 = momentScalarAmp2622P090Expected := by
  decide +kernel

theorem momentScalarAmp2622P090_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 200) 0) -
      (momentScalarAmp2622P090Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P090]
  have h := compactExp_real_error2620 momentPanelPhase2622P090 20 hsmall
  change |Real.exp (momentPanelPhase2622P090 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P090Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P090_replay] at h
  simpa only [momentPanelPhase_owner2622P090] using h

theorem momentScalarAmp2622P090_radius_le :
    (momentScalarAmp2622P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P090Expected]

def momentScalarGrow2622P090Input : RatPair2542 := (momentPanelGrowth2622P090 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P090Expected : RatState2542 :=
  ((((1100731403778888146086469116407509411987197376556389640899551761524468116095834869614295207980933 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((43604462016006227514097101089620148684304921919 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622P090_replay :
    compactExp2620 momentScalarGrow2622P090Input 20 = momentScalarGrow2622P090Expected := by
  decide +kernel

theorem momentScalarGrow2622P090_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P090Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P090]
  have h := compactExp_real_error2620 momentPanelGrowth2622P090 20 hsmall
  change |Real.exp (momentPanelGrowth2622P090 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P090Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P090_replay] at h
  simpa only [momentPanelGrowth_owner2622P090] using h

theorem momentScalarGrow2622P090_radius_le :
    (momentScalarGrow2622P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P090Expected]

end ConnesWeilRH.Dev
