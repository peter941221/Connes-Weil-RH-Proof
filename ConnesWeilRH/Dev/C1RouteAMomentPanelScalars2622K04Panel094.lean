import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P094 : ℚ := ((-337683551218343885273294458366283314527868155420426183 : ℚ) / 11394860129025842498393143522890879269852572496691200)

def momentPanelGrowth2622K04P094 : ℚ := ((945611459159388395220678487903514882286994333732309 : ℚ) / 7573975330882717300812006154077635840242321509580800)

theorem momentPanelPhase_owner2622K04P094 :
    (momentPanelPhase2622K04P094 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P094 :
    (momentPanelGrowth2622K04P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P094Input : RatPair2542 := (momentPanelPhase2622K04P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P094Expected : RatState2542 :=
  ((((18000348090253023384182469604409506657626409204705015762126109005644298594785594963 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((182550375631889317173177701573656415 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P094_replay :
    compactExp2620 momentScalarAmp2622K04P094Input 20 = momentScalarAmp2622K04P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K04P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P094_replay] at h
  simpa only [momentPanelPhase_owner2622K04P094] using h

theorem momentScalarAmp2622K04P094_radius_le :
    (momentScalarAmp2622K04P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P094Expected]

def momentScalarGrow2622K04P094Input : RatPair2542 := (momentPanelGrowth2622K04P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P094Expected : RatState2542 :=
  ((((2420027578395817717670189279476903075413002753545549533984897063804428021817460255735548636914265 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((766937261764179714804766736627660680222865507203 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P094_replay :
    compactExp2620 momentScalarGrow2622K04P094Input 20 = momentScalarGrow2622K04P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P094] using h

theorem momentScalarGrow2622K04P094_radius_le :
    (momentScalarGrow2622K04P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P094Expected]

end ConnesWeilRH.Dev
