import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P092 : ℚ := ((-906234512845109031398060345968661294034383144205109 : ℚ) / 30428920808491064664162656868663236307680158023680)

def momentPanelGrowth2622K04P092 : ℚ := ((1606069519598464370347892197112483830994334105099600687 : ℚ) / 14246798029297202450998847119161212992283181501015654400)

theorem momentPanelPhase_owner2622K04P092 :
    (momentPanelPhase2622K04P092 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P092, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P092 :
    (momentPanelGrowth2622K04P092 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P092, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P092Input : RatPair2542 := (momentPanelPhase2622K04P092 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P092Expected : RatState2542 :=
  ((((248562002283444823098711431246314966673625027160019801633021321799706712087386757681 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((157549360402562082320924188313043925 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P092_replay :
    compactExp2620 momentScalarAmp2622K04P092Input 20 = momentScalarAmp2622K04P092Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P092_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 40) 0) -
      (momentScalarAmp2622K04P092Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P092]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P092 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P092 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P092Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P092_replay] at h
  simpa only [momentPanelPhase_owner2622K04P092] using h

theorem momentScalarAmp2622K04P092_radius_le :
    (momentScalarAmp2622K04P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P092Expected]

def momentScalarGrow2622K04P092Input : RatPair2542 := (momentPanelGrowth2622K04P092 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P092Expected : RatState2542 :=
  ((((2390878365919467755902207747894943858507640340071545066764387181617785756504181484500475327408567 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3030798069790661109263034828841697258725570807007 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P092_replay :
    compactExp2620 momentScalarGrow2622K04P092Input 20 = momentScalarGrow2622K04P092Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P092_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P092Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P092]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P092 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P092 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P092Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P092_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P092] using h

theorem momentScalarGrow2622K04P092_radius_le :
    (momentScalarGrow2622K04P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P092Expected]

end ConnesWeilRH.Dev
