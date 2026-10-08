import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P046 : ℚ := ((-380674706992784072418915027254218531249151404873394919 : ℚ) / 9257413984429396980520254455043315353605771152588800)

def momentPanelGrowth2622K04P046 : ℚ := ((94540436148862904384935332379747748062380516191221 : ℚ) / 188824869744998492264011233758168206543437378355200)

theorem momentPanelPhase_owner2622K04P046 :
    (momentPanelPhase2622K04P046 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P046 :
    (momentPanelGrowth2622K04P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P046Input : RatPair2542 := (momentPanelPhase2622K04P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P046Expected : RatState2542 :=
  ((((369707038475158182362096145429133500850415376862132567241276017174088766076873 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3749424246530474675190853286721 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P046_replay :
    compactExp2620 momentScalarAmp2622K04P046Input 20 = momentScalarAmp2622K04P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K04P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P046_replay] at h
  simpa only [momentPanelPhase_owner2622K04P046] using h

theorem momentScalarAmp2622K04P046_radius_le :
    (momentScalarAmp2622K04P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P046Expected]

def momentScalarGrow2622K04P046Input : RatPair2542 := (momentPanelGrowth2622K04P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P046Expected : RatState2542 :=
  ((((440504417024814201027073938087219923059543912849384683096556653902491869825421690890700891640839 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4467243376121406178641714161506307275852788139757 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P046_replay :
    compactExp2620 momentScalarGrow2622K04P046Input 20 = momentScalarGrow2622K04P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P046] using h

theorem momentScalarGrow2622K04P046_radius_le :
    (momentScalarGrow2622K04P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P046Expected]

end ConnesWeilRH.Dev
