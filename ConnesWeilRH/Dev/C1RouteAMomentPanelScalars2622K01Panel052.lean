import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P052 : ℚ := ((-1098318788739675164700237613657650419407831844241 : ℚ) / 31399449239531117383282291327888893000420425728)

def momentPanelGrowth2622K01P052 : ℚ := ((17049896342846417640774264466773484221757842398166211 : ℚ) / 54417636171992708908028983500230279474082038887219200)

theorem momentPanelPhase_owner2622K01P052 :
    (momentPanelPhase2622K01P052 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-3 / 8) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P052, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P052 :
    (momentPanelGrowth2622K01P052 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P052, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P052Input : RatPair2542 := (momentPanelPhase2622K01P052 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P052Expected : RatState2542 :=
  ((((687728704970322893844669785392569033889728861483663923649616342731947237263308679 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1743657578542614812609978359567783 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P052_replay :
    compactExp2620 momentScalarAmp2622K01P052Input 20 = momentScalarAmp2622K01P052Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P052_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-3 / 8) 0) -
      (momentScalarAmp2622K01P052Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P052]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P052 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P052 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P052Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P052_replay] at h
  simpa only [momentPanelPhase_owner2622K01P052] using h

theorem momentScalarAmp2622K01P052_radius_le :
    (momentScalarAmp2622K01P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P052Expected]

def momentScalarGrow2622K01P052Input : RatPair2542 := (momentPanelGrowth2622K01P052 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P052Expected : RatState2542 :=
  ((((2921930385507958940946240715256536116526015111469961896354528000766869303381038466826790799915285 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3703985700259188009445886194206695962684324195531 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P052_replay :
    compactExp2620 momentScalarGrow2622K01P052Input 20 = momentScalarGrow2622K01P052Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P052_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P052Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P052]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P052 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P052 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P052Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P052_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P052] using h

theorem momentScalarGrow2622K01P052_radius_le :
    (momentScalarGrow2622K01P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P052Expected]

end ConnesWeilRH.Dev
