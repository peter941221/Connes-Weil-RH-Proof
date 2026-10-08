import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P004 : ℚ := ((-367405973921710002495439666133307761983044120012010803 : ℚ) / 3071151585164684472061219749061423634468394185523200)

def momentPanelGrowth2622K04P004 : ℚ := ((155338487096144714517077514503113589847315872699973709 : ℚ) / 20162299980549283451746088404622182943138146733260800)

theorem momentPanelPhase_owner2622K04P004 :
    (momentPanelPhase2622K04P004 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P004 :
    (momentPanelGrowth2622K04P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P004Input : RatPair2542 := (momentPanelPhase2622K04P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P004Expected : RatState2542 :=
  ((((236792843794638849217796989105341039670186941 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P004_replay :
    compactExp2620 momentScalarAmp2622K04P004Input 20 = momentScalarAmp2622K04P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K04P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P004_replay] at h
  simpa only [momentPanelPhase_owner2622K04P004] using h

theorem momentScalarAmp2622K04P004_radius_le :
    (momentScalarAmp2622K04P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P004Expected]

def momentScalarGrow2622K04P004Input : RatPair2542 := (momentPanelGrowth2622K04P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P004Expected : RatState2542 :=
  ((((2368909027238761463599636951117145484326814231361412343054006193396168259118670361532644625124373125 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1501463443102395353151865914199097369251680774912403 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P004_replay :
    compactExp2620 momentScalarGrow2622K04P004Input 20 = momentScalarGrow2622K04P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P004] using h

theorem momentScalarGrow2622K04P004_radius_le :
    (momentScalarGrow2622K04P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P004Expected]

end ConnesWeilRH.Dev
