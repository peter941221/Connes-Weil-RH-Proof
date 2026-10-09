import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P077 : ℚ := ((-1828272312590036450693907670335632600266386320453 : ℚ) / 59944403093650315004448010716878795728075358208)

def momentPanelGrowth2622K01P077 : ℚ := ((94911583263977012161726251988156611520969170278111051 : ℚ) / 1149511964088343488566787467281530559232426720310067200)

theorem momentPanelPhase_owner2622K01P077 :
    (momentPanelPhase2622K01P077 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P077 :
    (momentPanelGrowth2622K01P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P077Input : RatPair2542 := (momentPanelPhase2622K01P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P077Expected : RatState2542 :=
  ((((121296598131503506566387470904836174542124638296810866800219408747635135994693528035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((153766177893243432937190942455034601 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P077_replay :
    compactExp2620 momentScalarAmp2622K01P077Input 20 = momentScalarAmp2622K01P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K01P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P077_replay] at h
  simpa only [momentPanelPhase_owner2622K01P077] using h

theorem momentScalarAmp2622K01P077_radius_le :
    (momentScalarAmp2622K01P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P077Expected]

def momentScalarGrow2622K01P077Input : RatPair2542 := (momentPanelGrowth2622K01P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P077Expected : RatState2542 :=
  ((((1159917082975865478381737109788256344958617799366235658815049150534955580914424734930763316254669 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((367592367667416005943665615168181728128646369713 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P077_replay :
    compactExp2620 momentScalarGrow2622K01P077Input 20 = momentScalarGrow2622K01P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P077] using h

theorem momentScalarGrow2622K01P077_radius_le :
    (momentScalarGrow2622K01P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P077Expected]

end ConnesWeilRH.Dev
