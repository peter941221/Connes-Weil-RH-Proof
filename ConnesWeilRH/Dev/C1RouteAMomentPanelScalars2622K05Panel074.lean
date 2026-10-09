import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P074 : ℚ := ((-817069592678341659030394578639260725867 : ℚ) / 26393499617231918722682558098492620800)

def momentPanelGrowth2622K05P074 : ℚ := ((14445765158063341505683554201547409803 : ℚ) / 125372672603532252975066341736815001600)

theorem momentPanelPhase_owner2622K05P074 :
    (momentPanelPhase2622K05P074 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P074 :
    (momentPanelGrowth2622K05P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P074Input : RatPair2542 := (momentPanelPhase2622K05P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P074Expected : RatState2542 :=
  ((((76744135238038077121004867345481165115008567138614741964016381459562873916461366691 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24321905323000484012821074872999575 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P074_replay :
    compactExp2620 momentScalarAmp2622K05P074Input 20 = momentScalarAmp2622K05P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K05P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P074_replay] at h
  simpa only [momentPanelPhase_owner2622K05P074] using h

theorem momentScalarAmp2622K05P074_radius_le :
    (momentScalarAmp2622K05P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P074Expected]

def momentScalarGrow2622K05P074Input : RatPair2542 := (momentPanelGrowth2622K05P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P074Expected : RatState2542 :=
  ((((1198420296550816428927331365604511541205185848633818706988872981501388670961558310253090451426223 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3038356082627400735113483044216200999965579500429 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P074_replay :
    compactExp2620 momentScalarGrow2622K05P074Input 20 = momentScalarGrow2622K05P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P074] using h

theorem momentScalarGrow2622K05P074_radius_le :
    (momentScalarGrow2622K05P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P074Expected]

end ConnesWeilRH.Dev
