import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P048 : ℚ := ((-20916071 : ℚ) / 551850)

def momentPanelGrowth2622K06P048 : ℚ := ((43614481 : ℚ) / 105987025)

theorem momentPanelPhase_owner2622K06P048 :
    (momentPanelPhase2622K06P048 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P048 :
    (momentPanelGrowth2622K06P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P048Input : RatPair2542 := (momentPanelPhase2622K06P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P048Expected : RatState2542 :=
  ((((4623441996545295117138435679088899569033420015045208873440043474752335377999403 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((93777936397886628516886510701525 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P048_replay :
    compactExp2620 momentScalarAmp2622K06P048Input 20 = momentScalarAmp2622K06P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K06P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P048_replay] at h
  simpa only [momentPanelPhase_owner2622K06P048] using h

theorem momentScalarAmp2622K06P048_radius_le :
    (momentScalarAmp2622K06P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P048Expected]

def momentScalarGrow2622K06P048Input : RatPair2542 := (momentPanelGrowth2622K06P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P048Expected : RatState2542 :=
  ((((1611699818601046661374860596385246772074748124513661053186042182662831994325643247595446187247551 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1021535720322660469027495915934971613697758661115 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P048_replay :
    compactExp2620 momentScalarGrow2622K06P048Input 20 = momentScalarGrow2622K06P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P048] using h

theorem momentScalarGrow2622K06P048_radius_le :
    (momentScalarGrow2622K06P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P048Expected]

end ConnesWeilRH.Dev
