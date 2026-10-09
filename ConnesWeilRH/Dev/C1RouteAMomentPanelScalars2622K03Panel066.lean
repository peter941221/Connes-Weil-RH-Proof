import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P066 : ℚ := ((-73235178784059955591492614767308115445594529162817075 : ℚ) / 2301317015682173007576477229715877149825722780483584)

def momentPanelGrowth2622K03P066 : ℚ := ((5231901572015673664008718646590445804935299125689425 : ℚ) / 31689100595279635705383784115672851341378485858861056)

theorem momentPanelPhase_owner2622K03P066 :
    (momentPanelPhase2622K03P066 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P066 :
    (momentPanelGrowth2622K03P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P066Input : RatPair2542 := (momentPanelPhase2622K03P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P066Expected : RatState2542 :=
  ((((32283155787457281674303872940188269259089289747057570933363744530836262884494041943 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20462501912439828307770325471857669 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P066_replay :
    compactExp2620 momentScalarAmp2622K03P066Input 20 = momentScalarAmp2622K03P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K03P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P066_replay] at h
  simpa only [momentPanelPhase_owner2622K03P066] using h

theorem momentScalarAmp2622K03P066_radius_le :
    (momentScalarAmp2622K03P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P066Expected]

def momentScalarGrow2622K03P066Input : RatPair2542 := (momentPanelGrowth2622K03P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P066Expected : RatState2542 :=
  ((((2519422810961592191503697166023732708433240528135968872908245230782131163974995265638963385769561 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((399218416960050925636594769964196203360751737159 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P066_replay :
    compactExp2620 momentScalarGrow2622K03P066Input 20 = momentScalarGrow2622K03P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P066] using h

theorem momentScalarGrow2622K03P066_radius_le :
    (momentScalarGrow2622K03P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P066Expected]

end ConnesWeilRH.Dev
