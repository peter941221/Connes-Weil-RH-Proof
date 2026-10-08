import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P083 : ℚ := ((-116512684861159379954099584606152050705446076933938727 : ℚ) / 3789913523211405868162172563276189385150745385369600)

def momentPanelGrowth2622K04P083 : ℚ := ((645942516392678436319925069227337174072509445484061109 : ℚ) / 4710983111781811147735529921316721888081400856104140800)

theorem momentPanelPhase_owner2622K04P083 :
    (momentPanelPhase2622K04P083 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P083 :
    (momentPanelGrowth2622K04P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P083Input : RatPair2542 := (momentPanelPhase2622K04P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P083Expected : RatState2542 :=
  ((((5943402931965824052831506404082071738906323273738212657816516034805216097094236727 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((120550067021726200169994908265242727 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P083_replay :
    compactExp2620 momentScalarAmp2622K04P083Input 20 = momentScalarAmp2622K04P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K04P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P083_replay] at h
  simpa only [momentPanelPhase_owner2622K04P083] using h

theorem momentScalarAmp2622K04P083_radius_le :
    (momentScalarAmp2622K04P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P083Expected]

def momentScalarGrow2622K04P083Input : RatPair2542 := (momentPanelGrowth2622K04P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P083Expected : RatState2542 :=
  ((((2449889733724933867031586521795646311880280220354861381935823576600228412904320450326917377731143 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((776400946338400120534784937673556157917346799475 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P083_replay :
    compactExp2620 momentScalarGrow2622K04P083Input 20 = momentScalarGrow2622K04P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P083] using h

theorem momentScalarGrow2622K04P083_radius_le :
    (momentScalarGrow2622K04P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P083Expected]

end ConnesWeilRH.Dev
