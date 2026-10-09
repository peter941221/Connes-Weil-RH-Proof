import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P091 : ℚ := ((-2432004772759398228782068104654595584963 : ℚ) / 81111384245963395192407452617906585600)

def momentPanelGrowth2622K20P091 : ℚ := ((58049126904026844160554819817806590123 : ℚ) / 2111061137620238090820350137140353433600)

theorem momentPanelPhase_owner2622K20P091 :
    (momentPanelPhase2622K20P091 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P091 :
    (momentPanelGrowth2622K20P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P091Input : RatPair2542 := (momentPanelPhase2622K20P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P091Expected : RatState2542 :=
  ((((203198986414242941847291588759454273579497022749768293740354026745515318420859206631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8049771335252284192969075998114839 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K20P091_replay :
    compactExp2620 momentScalarAmp2622K20P091Input 20 = momentScalarAmp2622K20P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K20P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P091_replay] at h
  simpa only [momentPanelPhase_owner2622K20P091] using h

theorem momentScalarAmp2622K20P091_radius_le :
    (momentScalarAmp2622K20P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P091Expected]

def momentScalarGrow2622K20P091Input : RatPair2542 := (momentPanelGrowth2622K20P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P091Expected : RatState2542 :=
  ((((2195536547689569656073945817892086333540003712027661590662103606494063074877322906661282861818137 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1391586574758215454862030521612244424391801233233 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K20P091_replay :
    compactExp2620 momentScalarGrow2622K20P091Input 20 = momentScalarGrow2622K20P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P091] using h

theorem momentScalarGrow2622K20P091_radius_le :
    (momentScalarGrow2622K20P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P091Expected]

end ConnesWeilRH.Dev
