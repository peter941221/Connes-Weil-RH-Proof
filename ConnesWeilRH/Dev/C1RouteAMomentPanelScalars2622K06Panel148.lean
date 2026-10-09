import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P148 : ℚ := ((-56921613 : ℚ) / 1315550)

def momentPanelGrowth2622K06P148 : ℚ := ((309165787 : ℚ) / 354144675)

theorem momentPanelPhase_owner2622K06P148 :
    (momentPanelPhase2622K06P148 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (117 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P148 :
    (momentPanelGrowth2622K06P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P148Input : RatPair2542 := (momentPanelPhase2622K06P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P148Expected : RatState2542 :=
  ((((172736603876478970448091017948520639628258015706726672916105469940048661045695 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((109489952116290379177197003943 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P148_replay :
    compactExp2620 momentScalarAmp2622K06P148Input 20 = momentScalarAmp2622K06P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K06P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P148_replay] at h
  simpa only [momentPanelPhase_owner2622K06P148] using h

theorem momentScalarAmp2622K06P148_radius_le :
    (momentScalarAmp2622K06P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P148Expected]

def momentScalarGrow2622K06P148Input : RatPair2542 := (momentPanelGrowth2622K06P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P148Expected : RatState2542 :=
  ((((1278423132900883323555155145466785745047050988348661076219392036830180605811712743364841354264595 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6482370010164551446971108396251892040010943102607 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P148_replay :
    compactExp2620 momentScalarGrow2622K06P148Input 20 = momentScalarGrow2622K06P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P148] using h

theorem momentScalarGrow2622K06P148_radius_le :
    (momentScalarGrow2622K06P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P148Expected]

end ConnesWeilRH.Dev
