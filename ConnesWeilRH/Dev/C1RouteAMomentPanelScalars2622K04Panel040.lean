import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P040 : ℚ := ((-382948146729943128734446987513258566609601059702350427 : ℚ) / 8620290614405456489615835598281060724724513059635200)

def momentPanelGrowth2622K04P040 : ℚ := ((268907532259062169032605348802438508409839995421 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K04P040 :
    (momentPanelPhase2622K04P040 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P040 :
    (momentPanelGrowth2622K04P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P040Input : RatPair2542 := (momentPanelPhase2622K04P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P040Expected : RatState2542 :=
  ((((108763353316259390293591593380410950292200712594685916435674534120636144072325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((34470547316441254558197764353 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P040_replay :
    compactExp2620 momentScalarAmp2622K04P040Input 20 = momentScalarAmp2622K04P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K04P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P040_replay] at h
  simpa only [momentPanelPhase_owner2622K04P040] using h

theorem momentScalarAmp2622K04P040_radius_le :
    (momentScalarAmp2622K04P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P040Expected]

def momentScalarGrow2622K04P040Input : RatPair2542 := (momentPanelGrowth2622K04P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P040Expected : RatState2542 :=
  ((((2001335133382166530590255564803516196247227254512063604311815404808693219417238476593105256493337 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2536992163586244601090499810136575478165836427611 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P040_replay :
    compactExp2620 momentScalarGrow2622K04P040Input 20 = momentScalarGrow2622K04P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P040] using h

theorem momentScalarGrow2622K04P040_radius_le :
    (momentScalarGrow2622K04P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P040Expected]

end ConnesWeilRH.Dev
