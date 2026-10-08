import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P148 : ℚ := ((-300932068706958992093203606473819967703985110784804051 : ℚ) / 7510462808557302086104912428437133306673289284812800)

def momentPanelGrowth2622K04P148 : ℚ := ((1875616589026116158773831192505884305333664954695455749 : ℚ) / 2021808681111408130561701362831005535953393915055308800)

theorem momentPanelPhase_owner2622K04P148 :
    (momentPanelPhase2622K04P148 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (117 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P148 :
    (momentPanelGrowth2622K04P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P148Input : RatPair2542 := (momentPanelPhase2622K04P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P148Expected : RatState2542 :=
  ((((1059333771676378059417576387023078019518704748178582588159704987359143237994117 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((10743333668216812468755279910371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P148_replay :
    compactExp2620 momentScalarAmp2622K04P148Input 20 = momentScalarAmp2622K04P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K04P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P148_replay] at h
  simpa only [momentPanelPhase_owner2622K04P148] using h

theorem momentScalarAmp2622K04P148_radius_le :
    (momentScalarAmp2622K04P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P148Expected]

def momentScalarGrow2622K04P148Input : RatPair2542 := (momentPanelGrowth2622K04P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P148Expected : RatState2542 :=
  ((((2700600326986263740044573676217691295926025201443494245239768556596821281770994405738197909760745 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6846829193456385851863861974390858509147155072401 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P148_replay :
    compactExp2620 momentScalarGrow2622K04P148Input 20 = momentScalarGrow2622K04P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P148] using h

theorem momentScalarGrow2622K04P148_radius_le :
    (momentScalarGrow2622K04P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P148Expected]

end ConnesWeilRH.Dev
