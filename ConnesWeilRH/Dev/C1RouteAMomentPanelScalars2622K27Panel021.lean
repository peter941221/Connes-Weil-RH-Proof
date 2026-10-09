import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K27
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K27P021 : ℚ := ((-826524797482425961321127410287253148581 : ℚ) / 14353861276504287159027469735113523200)

def momentPanelGrowth2622K27P021 : ℚ := ((42415691519994936913018573751086177152649 : ℚ) / 27834687528149471998910075183234337996800)

theorem momentPanelPhase_owner2622K27P021 :
    (momentPanelPhase2622K27P021 : ℝ) = momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-137 / 200) 0 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K27P021 :
    (momentPanelGrowth2622K27P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K27P021Input : RatPair2542 := (momentPanelPhase2622K27P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K27P021Expected : RatState2542 :=
  ((((104954446341217624098450343331012475133565148284751436665627233636900871 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((670989346425574061542061 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K27P021_replay :
    compactExp2620 momentScalarAmp2622K27P021Input 20 = momentScalarAmp2622K27P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K27P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K27P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K27P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K27P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K27P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K27P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K27P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K27P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K27P021_replay] at h
  simpa only [momentPanelPhase_owner2622K27P021] using h

theorem momentScalarAmp2622K27P021_radius_le :
    (momentScalarAmp2622K27P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarAmp2622K27P021Expected]

def momentScalarGrow2622K27P021Input : RatPair2542 := (momentPanelGrowth2622K27P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K27P021Expected : RatState2542 :=
  ((((4901908363268017517689237486603011115135185552734402090393814033184042867237036812512873575465893 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((12427796097214960151836347633798930099148869933575 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K27P021_replay :
    compactExp2620 momentScalarGrow2622K27P021Input 20 = momentScalarGrow2622K27P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K27P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K27P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K27P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K27P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K27P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K27P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K27P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K27P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K27P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K27P021] using h

theorem momentScalarGrow2622K27P021_radius_le :
    (momentScalarGrow2622K27P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarGrow2622K27P021Expected]

end ConnesWeilRH.Dev
