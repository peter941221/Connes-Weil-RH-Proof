import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P149 : ℚ := ((-796628092721537245889535830875486252717 : ℚ) / 17469239391625183736145767532645580800)

def momentPanelGrowth2622K05P149 : ℚ := ((905628096501810419302283676421089 : ℚ) / 1014120480182583521197362564300800)

theorem momentPanelPhase_owner2622K05P149 :
    (momentPanelPhase2622K05P149 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P149 :
    (momentPanelGrowth2622K05P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P149Input : RatPair2542 := (momentPanelPhase2622K05P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P149Expected : RatState2542 :=
  ((((16748469354900979548602450365923709093656016913731600146058990868575564119595 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((10616669752687219753294830041 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P149_replay :
    compactExp2620 momentScalarAmp2622K05P149Input 20 = momentScalarAmp2622K05P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K05P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P149_replay] at h
  simpa only [momentPanelPhase_owner2622K05P149] using h

theorem momentScalarAmp2622K05P149_radius_le :
    (momentScalarAmp2622K05P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P149Expected]

def momentScalarGrow2622K05P149Input : RatPair2542 := (momentPanelGrowth2622K05P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P149Expected : RatState2542 :=
  ((((2608564111754454708780858942392406571176048563610421620256484201753085452091140233125713255214575 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6613490091626933566241591605889977441690202026715 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P149_replay :
    compactExp2620 momentScalarGrow2622K05P149Input 20 = momentScalarGrow2622K05P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P149] using h

theorem momentScalarGrow2622K05P149_radius_le :
    (momentScalarGrow2622K05P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P149Expected]

end ConnesWeilRH.Dev
