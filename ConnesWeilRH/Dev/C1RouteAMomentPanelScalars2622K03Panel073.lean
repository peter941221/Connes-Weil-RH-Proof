import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P073 : ℚ := ((-219572465265572141781685928740752198244033833238070775 : ℚ) / 7108561276272845431277947565727911072228998897467392)

def momentPanelGrowth2622K03P073 : ℚ := ((319069209702585943016010828337813512900989834806281475 : ℚ) / 2871348965574358068662134893738364224709721819606679552)

theorem momentPanelPhase_owner2622K03P073 :
    (momentPanelPhase2622K03P073 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P073 :
    (momentPanelGrowth2622K03P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P073Input : RatPair2542 := (momentPanelPhase2622K03P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P073Expected : RatState2542 :=
  ((((82207918512445957318159191064326944436509741918825505609554480012806930083871711791 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26053496772284112657777159828157215 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P073_replay :
    compactExp2620 momentScalarAmp2622K03P073Input 20 = momentScalarAmp2622K03P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K03P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P073_replay] at h
  simpa only [momentPanelPhase_owner2622K03P073] using h

theorem momentScalarAmp2622K03P073_radius_le :
    (momentScalarAmp2622K03P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P073Expected]

def momentScalarGrow2622K03P073Input : RatPair2542 := (momentPanelGrowth2622K03P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P073Expected : RatState2542 :=
  ((((2387031545170781598175577140009895826231928466839329602364813580972021457365221402171973804078369 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3025921650330658201080510498891598295473628906899 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P073_replay :
    compactExp2620 momentScalarGrow2622K03P073Input 20 = momentScalarGrow2622K03P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P073] using h

theorem momentScalarGrow2622K03P073_radius_le :
    (momentScalarGrow2622K03P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P073Expected]

end ConnesWeilRH.Dev
