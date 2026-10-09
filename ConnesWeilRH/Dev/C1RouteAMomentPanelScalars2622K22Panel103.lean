import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K22
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K22P103 : ℚ := ((-2417235073538043451202900810410303038027 : ℚ) / 79651050754500474921883250525313433600)

def momentPanelGrowth2622K22P103 : ℚ := ((208923228450046598010477673337989365323 : ℚ) / 2030742795589777475941519022047730073600)

theorem momentPanelPhase_owner2622K22P103 :
    (momentPanelPhase2622K22P103 : ℝ) = momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K22P103 :
    (momentPanelGrowth2622K22P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K22P103Input : RatPair2542 := (momentPanelPhase2622K22P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K22P103Expected : RatState2542 :=
  ((((8822497834896825319416283875374866004205811788025878420678188274722295613542263827 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((44736673451143974833241958620309587 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K22P103_replay :
    compactExp2620 momentScalarAmp2622K22P103Input 20 = momentScalarAmp2622K22P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K22P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K22P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K22P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K22P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K22P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K22P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K22P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K22P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K22P103_replay] at h
  simpa only [momentPanelPhase_owner2622K22P103] using h

theorem momentScalarAmp2622K22P103_radius_le :
    (momentScalarAmp2622K22P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarAmp2622K22P103Expected]

def momentScalarGrow2622K22P103Input : RatPair2542 := (momentPanelGrowth2622K22P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K22P103Expected : RatState2542 :=
  ((((1183719823513704095443716150230899619447057790624690219954424087876773942813004347802755231328755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3001085995109217467983165447977104454820280413209 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K22P103_replay :
    compactExp2620 momentScalarGrow2622K22P103Input 20 = momentScalarGrow2622K22P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K22P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K22P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K22P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K22P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K22P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K22P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K22P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K22P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K22P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K22P103] using h

theorem momentScalarGrow2622K22P103_radius_le :
    (momentScalarGrow2622K22P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarGrow2622K22P103Expected]

end ConnesWeilRH.Dev
