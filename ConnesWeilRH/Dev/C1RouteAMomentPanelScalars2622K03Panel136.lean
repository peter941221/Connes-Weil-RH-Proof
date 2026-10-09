import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P136 : ℚ := ((-218436835226896179913951695344124511614493321438267725 : ℚ) / 5727442228995142173575465398811023618654142644355072)

def momentPanelGrowth2622K03P136 : ℚ := ((864103418811755986341485883356988905670254432045097475 : ℚ) / 1848180899311739553686099216050348808308996564920041472)

theorem momentPanelPhase_owner2622K03P136 :
    (momentPanelPhase2622K03P136 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (93 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P136 :
    (momentPanelGrowth2622K03P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P136Input : RatPair2542 := (momentPanelPhase2622K03P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P136Expected : RatState2542 :=
  ((((58371302776423930905920839654692701248691751554040298838946612537643849656247875 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((73997110780363804078146763915625 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P136_replay :
    compactExp2620 momentScalarAmp2622K03P136Input 20 = momentScalarAmp2622K03P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K03P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P136_replay] at h
  simpa only [momentPanelPhase_owner2622K03P136] using h

theorem momentScalarAmp2622K03P136_radius_le :
    (momentScalarAmp2622K03P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P136Expected]

def momentScalarGrow2622K03P136Input : RatPair2542 := (momentPanelGrowth2622K03P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P136Expected : RatState2542 :=
  ((((3409179049801098768160078188905632234574857592283330997104106140223268137420256740848445872540737 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((135051435681722675533717569349165745418115430873 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K03P136_replay :
    compactExp2620 momentScalarGrow2622K03P136Input 20 = momentScalarGrow2622K03P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P136] using h

theorem momentScalarGrow2622K03P136_radius_le :
    (momentScalarGrow2622K03P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P136Expected]

end ConnesWeilRH.Dev
