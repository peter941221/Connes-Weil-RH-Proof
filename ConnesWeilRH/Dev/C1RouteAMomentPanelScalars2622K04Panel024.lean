import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P024 : ℚ := ((-127659329995130914885087187098071596268176756565512681 : ℚ) / 2173127336914094514899346217083801294656370009702400)

def momentPanelGrowth2622K04P024 : ℚ := ((380153026763114915980436668088724162446150845073153367 : ℚ) / 284153740360984235235644376058235830642227429140070400)

theorem momentPanelPhase_owner2622K04P024 :
    (momentPanelPhase2622K04P024 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P024 :
    (momentPanelGrowth2622K04P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P024Input : RatPair2542 := (momentPanelPhase2622K04P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P024Expected : RatState2542 :=
  ((((65641152520185685813311584013566792124201714633956611918010615536752283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1250533173720465600886369 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P024_replay :
    compactExp2620 momentScalarAmp2622K04P024Input 20 = momentScalarAmp2622K04P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K04P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P024_replay] at h
  simpa only [momentPanelPhase_owner2622K04P024] using h

theorem momentScalarAmp2622K04P024_radius_le :
    (momentScalarAmp2622K04P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P024Expected]

def momentScalarGrow2622K04P024Input : RatPair2542 := (momentPanelGrowth2622K04P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P024Expected : RatState2542 :=
  ((((4069924463607150364532092358139292960384009408268348031264147378536352420674417572667572018049721 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5159235606676177382297271975297341146409465572465 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P024_replay :
    compactExp2620 momentScalarGrow2622K04P024Input 20 = momentScalarGrow2622K04P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P024] using h

theorem momentScalarGrow2622K04P024_radius_le :
    (momentScalarGrow2622K04P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P024Expected]

end ConnesWeilRH.Dev
