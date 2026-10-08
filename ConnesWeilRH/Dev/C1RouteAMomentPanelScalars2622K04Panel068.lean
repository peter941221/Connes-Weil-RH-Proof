import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P068 : ℚ := ((-121570765244723585591073292055086394912130069744097937 : ℚ) / 3630061781628338361483644534697845929875877763481600)

def momentPanelGrowth2622K04P068 : ℚ := ((64747818813320856224108173372550479102480390359576269 : ℚ) / 269256985293135049573086622080703670105746149526732800)

theorem momentPanelPhase_owner2622K04P068 :
    (momentPanelPhase2622K04P068 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-43 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P068 :
    (momentPanelGrowth2622K04P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P068Input : RatPair2542 := (momentPanelPhase2622K04P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P068Expected : RatState2542 :=
  ((((6096447957595380349272205981623580677558731312326355066928684526716281950668712123 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3864206372746603466527575935836053 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P068_replay :
    compactExp2620 momentScalarAmp2622K04P068Input 20 = momentScalarAmp2622K04P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K04P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P068_replay] at h
  simpa only [momentPanelPhase_owner2622K04P068] using h

theorem momentScalarAmp2622K04P068_radius_le :
    (momentScalarAmp2622K04P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P068Expected]

def momentScalarGrow2622K04P068Input : RatPair2542 := (momentPanelGrowth2622K04P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P068Expected : RatState2542 :=
  ((((2716644108249977821925248981717219555932458735286965089184689941016401297921810499523875558394259 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1721877372338983347715176094828704603355292390075 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P068_replay :
    compactExp2620 momentScalarGrow2622K04P068Input 20 = momentScalarGrow2622K04P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P068] using h

theorem momentScalarGrow2622K04P068_radius_le :
    (momentScalarGrow2622K04P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P068Expected]

end ConnesWeilRH.Dev
