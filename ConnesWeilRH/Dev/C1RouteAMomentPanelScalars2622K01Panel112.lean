import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P112 : ℚ := ((-684170574380769263194491904570136149935315991751817 : ℚ) / 21679892452203530593275363875937831121653921218560)

def momentPanelGrowth2622K01P112 : ℚ := ((166120074054066301001301121595167014662430636753937531 : ℚ) / 1066865759194512175694226359934588093865047394300723200)

theorem momentPanelPhase_owner2622K01P112 :
    (momentPanelPhase2622K01P112 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P112 :
    (momentPanelGrowth2622K01P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P112Input : RatPair2542 := (momentPanelPhase2622K01P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P112Expected : RatState2542 :=
  ((((42092323222557991394246676695337850212370298454823649342521686127995689353763572829 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((53359964692562735993260024106877871 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P112_replay :
    compactExp2620 momentScalarAmp2622K01P112Input 20 = momentScalarAmp2622K01P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K01P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P112_replay] at h
  simpa only [momentPanelPhase_owner2622K01P112] using h

theorem momentScalarAmp2622K01P112_radius_le :
    (momentScalarAmp2622K01P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P112Expected]

def momentScalarGrow2622K01P112Input : RatPair2542 := (momentPanelGrowth2622K01P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P112Expected : RatState2542 :=
  ((((2495869981248956373948014094093573391009678644189085056359569955667768737524752502850639719142677 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1581945304999622132305575560364350108622291794891 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P112_replay :
    compactExp2620 momentScalarGrow2622K01P112Input 20 = momentScalarGrow2622K01P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P112] using h

theorem momentScalarGrow2622K01P112_radius_le :
    (momentScalarGrow2622K01P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P112Expected]

end ConnesWeilRH.Dev
