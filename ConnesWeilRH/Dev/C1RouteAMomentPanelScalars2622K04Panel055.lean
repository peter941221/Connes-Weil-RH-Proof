import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P055 : ℚ := ((-375403398711587103753512553515263642954060158046793757 : ℚ) / 10058956288653064049722587855486151822198321656627200)

def momentPanelGrowth2622K04P055 : ℚ := ((2153577638452675528783514643812953066860028950448309 : ℚ) / 5861278099635565443542062990738241676583025560780800)

theorem momentPanelPhase_owner2622K04P055 :
    (momentPanelPhase2622K04P055 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P055 :
    (momentPanelGrowth2622K04P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P055Input : RatPair2542 := (momentPanelPhase2622K04P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P055Expected : RatState2542 :=
  ((((132309962415585517237121058372006440339799315425030961814351268172656249963193075 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5241524227806389246608896560903 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K04P055_replay :
    compactExp2620 momentScalarAmp2622K04P055Input 20 = momentScalarAmp2622K04P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K04P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P055_replay] at h
  simpa only [momentPanelPhase_owner2622K04P055] using h

theorem momentScalarAmp2622K04P055_radius_le :
    (momentScalarAmp2622K04P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P055Expected]

def momentScalarGrow2622K04P055Input : RatPair2542 := (momentPanelGrowth2622K04P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P055Expected : RatState2542 :=
  ((((3084388531689414627594713578537900290312913225176079929102066913012287904680332086618183753974105 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1954962801740875001384452124085797683654101107547 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P055_replay :
    compactExp2620 momentScalarGrow2622K04P055Input 20 = momentScalarGrow2622K04P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P055] using h

theorem momentScalarGrow2622K04P055_radius_le :
    (momentScalarGrow2622K04P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P055Expected]

end ConnesWeilRH.Dev
