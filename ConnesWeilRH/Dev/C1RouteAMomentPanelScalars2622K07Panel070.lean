import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P070 : ℚ := ((-102270358265896118841390366011054937075 : ℚ) / 3121787356555650504972265128938438656)

def momentPanelGrowth2622K07P070 : ℚ := ((25670756233415393744689314585425 : ℚ) / 121694457621910022543683507716096)

theorem momentPanelPhase_owner2622K07P070 :
    (momentPanelPhase2622K07P070 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P070 :
    (momentPanelGrowth2622K07P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P070Input : RatPair2542 := (momentPanelPhase2622K07P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P070Expected : RatState2542 :=
  ((((790509896218161901046451053267250251087933091302062570877385502033181930699307533 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((4008486611721850648156405289537007 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P070_replay :
    compactExp2620 momentScalarAmp2622K07P070Input 20 = momentScalarAmp2622K07P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K07P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P070_replay] at h
  simpa only [momentPanelPhase_owner2622K07P070] using h

theorem momentScalarAmp2622K07P070_radius_le :
    (momentScalarAmp2622K07P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P070Expected]

def momentScalarGrow2622K07P070Input : RatPair2542 := (momentPanelGrowth2622K07P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P070Expected : RatState2542 :=
  ((((1318804974934531421495974102931524283805259736728241802002953097735576358839034218783624398410761 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3343567163486661621285227041782356512123806527871 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P070_replay :
    compactExp2620 momentScalarGrow2622K07P070Input 20 = momentScalarGrow2622K07P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P070] using h

theorem momentScalarGrow2622K07P070_radius_le :
    (momentScalarGrow2622K07P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P070Expected]

end ConnesWeilRH.Dev
