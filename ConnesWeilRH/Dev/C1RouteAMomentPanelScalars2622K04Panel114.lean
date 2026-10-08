import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P114 : ℚ := ((-105879430223110947892777186143146066669975864883534341 : ℚ) / 3577539066536759037860699611022104508856992687718400)

def momentPanelGrowth2622K04P114 : ℚ := ((568114916463268669867319176631667187856985813649 : ℚ) / 2140871539058939821587428954174242704574119936000)

theorem momentPanelPhase_owner2622K04P114 :
    (momentPanelPhase2622K04P114 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (49 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P114, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P114 :
    (momentPanelGrowth2622K04P114 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P114, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P114Input : RatPair2542 := (momentPanelPhase2622K04P114 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P114Expected : RatState2542 :=
  ((((149747997728716272314258016195245776040904732703567317535311257422118780974344920515 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((23729187137218937129085215223918975 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K04P114_replay :
    compactExp2620 momentScalarAmp2622K04P114Input 20 = momentScalarAmp2622K04P114Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P114_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (49 / 200) 0) -
      (momentScalarAmp2622K04P114Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P114]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P114 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P114 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P114Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P114_replay] at h
  simpa only [momentPanelPhase_owner2622K04P114] using h

theorem momentScalarAmp2622K04P114_radius_le :
    (momentScalarAmp2622K04P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P114Expected]

def momentScalarGrow2622K04P114Input : RatPair2542 := (momentPanelGrowth2622K04P114 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P114Expected : RatState2542 :=
  ((((2785131357738390842300465890533303395309130455885847281661781758773582764856379931001420332242793 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3530572543859130486216190768285303398065110940537 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P114_replay :
    compactExp2620 momentScalarGrow2622K04P114Input 20 = momentScalarGrow2622K04P114Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P114_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P114Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P114]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P114 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P114 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P114Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P114_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P114] using h

theorem momentScalarGrow2622K04P114_radius_le :
    (momentScalarGrow2622K04P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P114Expected]

end ConnesWeilRH.Dev
