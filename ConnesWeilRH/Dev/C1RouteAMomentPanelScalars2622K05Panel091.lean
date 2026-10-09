import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P091 : ℚ := ((-2432172186656481897397457568789338129403 : ℚ) / 81111384245963395192407452617906585600)

def momentPanelGrowth2622K05P091 : ℚ := ((55144306778661393637587655230965315363 : ℚ) / 2111061137620238090820350137140353433600)

theorem momentPanelPhase_owner2622K05P091 :
    (momentPanelPhase2622K05P091 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P091 :
    (momentPanelGrowth2622K05P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P091Input : RatPair2542 := (momentPanelPhase2622K05P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P091Expected : RatState2542 :=
  ((((202780016232249517018528598082311840464051119544561791076047813219588567606536943453 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((64265390061100345626352190583913353 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P091_replay :
    compactExp2620 momentScalarAmp2622K05P091Input 20 = momentScalarAmp2622K05P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K05P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P091_replay] at h
  simpa only [momentPanelPhase_owner2622K05P091] using h

theorem momentScalarAmp2622K05P091_radius_le :
    (momentScalarAmp2622K05P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P091Expected]

def momentScalarGrow2622K05P091Input : RatPair2542 := (momentPanelGrowth2622K05P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P091Expected : RatState2542 :=
  ((((1096258783467523355357031433626503160629539006602223839814072201984318447084434535596535944275115 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1389673070249227172602331792170270656657085171399 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P091_replay :
    compactExp2620 momentScalarGrow2622K05P091Input 20 = momentScalarGrow2622K05P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P091] using h

theorem momentScalarGrow2622K05P091_radius_le :
    (momentScalarGrow2622K05P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P091Expected]

end ConnesWeilRH.Dev
