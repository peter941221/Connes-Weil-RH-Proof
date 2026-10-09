import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P127 : ℚ := ((-1093933667256679212605289635416774110076066970223 : ℚ) / 31399449239531117383282291327888893000420425728)

def momentPanelGrowth2622K01P127 : ℚ := ((17049896342846417640774264466773484221757842398166211 : ℚ) / 54417636171992708908028983500230279474082038887219200)

theorem momentPanelPhase_owner2622K01P127 :
    (momentPanelPhase2622K01P127 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P127 :
    (momentPanelGrowth2622K01P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P127Input : RatPair2542 := (momentPanelPhase2622K01P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P127Expected : RatState2542 :=
  ((((395402113299876952459390937390816642764416541807556334427765788787677687638351501 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1002496761433664055665151923135751 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P127_replay :
    compactExp2620 momentScalarAmp2622K01P127Input 20 = momentScalarAmp2622K01P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K01P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P127_replay] at h
  simpa only [momentPanelPhase_owner2622K01P127] using h

theorem momentScalarAmp2622K01P127_radius_le :
    (momentScalarAmp2622K01P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P127Expected]

def momentScalarGrow2622K01P127Input : RatPair2542 := (momentPanelGrowth2622K01P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P127Expected : RatState2542 :=
  ((((2921930385507958940946240715256536116526015111469961896354528000766869303381038466826790799915285 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3703985700259188009445886194206695962684324195531 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P127_replay :
    compactExp2620 momentScalarGrow2622K01P127Input 20 = momentScalarGrow2622K01P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P127] using h

theorem momentScalarGrow2622K01P127_radius_le :
    (momentScalarGrow2622K01P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P127Expected]

end ConnesWeilRH.Dev
