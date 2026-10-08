import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P031 : ℚ := ((-384146823791901750814773658861937697759733268735195949 : ℚ) / 7510462808557302086104912428437133306673289284812800)

def momentPanelGrowth2622K04P031 : ℚ := ((1875616589026116158773831192505884305333664954695455749 : ℚ) / 2021808681111408130561701362831005535953393915055308800)

theorem momentPanelPhase_owner2622K04P031 :
    (momentPanelPhase2622K04P031 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P031 :
    (momentPanelGrowth2622K04P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P031Input : RatPair2542 := (momentPanelPhase2622K04P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P031Expected : RatState2542 :=
  ((((130679590468991093188936099770786004845562048122238061982848980171688110087 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((21010249203365428887228473 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P031_replay :
    compactExp2620 momentScalarAmp2622K04P031Input 20 = momentScalarAmp2622K04P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K04P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P031_replay] at h
  simpa only [momentPanelPhase_owner2622K04P031] using h

theorem momentScalarAmp2622K04P031_radius_le :
    (momentScalarAmp2622K04P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P031Expected]

def momentScalarGrow2622K04P031Input : RatPair2542 := (momentPanelGrowth2622K04P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P031Expected : RatState2542 :=
  ((((2700600326986263740044573676217691295926025201443494245239768556596821281770994405738197909760745 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6846829193456385851863861974390858509147155072401 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P031_replay :
    compactExp2620 momentScalarGrow2622K04P031Input 20 = momentScalarGrow2622K04P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P031] using h

theorem momentScalarGrow2622K04P031_radius_le :
    (momentScalarGrow2622K04P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P031Expected]

end ConnesWeilRH.Dev
