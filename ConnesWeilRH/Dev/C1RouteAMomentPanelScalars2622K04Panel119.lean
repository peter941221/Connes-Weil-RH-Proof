import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P119 : ℚ := ((-104472553203296400248941595174064015822973388300658911 : ℚ) / 3474777232661929926424503021221740859037434930790400)

def momentPanelGrowth2622K04P119 : ℚ := ((368830308590274517841164246284639195295628070702087 : ℚ) / 1181903814329805377504366611301126922438552479334400)

theorem momentPanelPhase_owner2622K04P119 :
    (momentPanelPhase2622K04P119 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P119 :
    (momentPanelGrowth2622K04P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P119Input : RatPair2542 := (momentPanelPhase2622K04P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P119Expected : RatState2542 :=
  ((((11694808632730595603942408265737837431740301891903032064066759891318060790949259533 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((237205700263665348520145285657431125 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P119_replay :
    compactExp2620 momentScalarAmp2622K04P119Input 20 = momentScalarAmp2622K04P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K04P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P119_replay] at h
  simpa only [momentPanelPhase_owner2622K04P119] using h

theorem momentScalarAmp2622K04P119_radius_le :
    (momentScalarAmp2622K04P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P119Expected]

def momentScalarGrow2622K04P119Input : RatPair2542 := (momentPanelGrowth2622K04P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P119Expected : RatState2542 :=
  ((((729569286956979536530367333959459208746349844830031740845339479258703870098174205293226736975507 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1849677338559397045831062000883648816866817734453 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P119_replay :
    compactExp2620 momentScalarGrow2622K04P119Input 20 = momentScalarGrow2622K04P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P119] using h

theorem momentScalarGrow2622K04P119_radius_le :
    (momentScalarGrow2622K04P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P119Expected]

end ConnesWeilRH.Dev
