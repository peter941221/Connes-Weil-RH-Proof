import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P048 : ℚ := ((-126561400952249030609901744446515508705455023663407417 : ℚ) / 3150506556879135841448060448962815564051274897817600)

def momentPanelGrowth2622K04P048 : ℚ := ((282092197496475435610380251901187615855591522341824487 : ℚ) / 605078947552075550250886326004771509028706304026214400)

theorem momentPanelPhase_owner2622K04P048 :
    (momentPanelPhase2622K04P048 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P048 :
    (momentPanelGrowth2622K04P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P048Input : RatPair2542 := (momentPanelPhase2622K04P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P048Expected : RatState2542 :=
  ((((3821148035345220308454451280976370088009609323319245251737170600808765657771195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2422033692940803156520474085327 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P048_replay :
    compactExp2620 momentScalarAmp2622K04P048Input 20 = momentScalarAmp2622K04P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K04P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P048_replay] at h
  simpa only [momentPanelPhase_owner2622K04P048] using h

theorem momentScalarAmp2622K04P048_radius_le :
    (momentScalarAmp2622K04P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P048Expected]

def momentScalarGrow2622K04P048Input : RatPair2542 := (momentPanelGrowth2622K04P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P048Expected : RatState2542 :=
  ((((851157364315141840620673587134044631770753105613308994678528244909136333510418262491817646628933 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1078969664042078262860113676581136505793032085567 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P048_replay :
    compactExp2620 momentScalarGrow2622K04P048Input 20 = momentScalarGrow2622K04P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P048] using h

theorem momentScalarGrow2622K04P048_radius_le :
    (momentScalarGrow2622K04P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P048Expected]

end ConnesWeilRH.Dev
