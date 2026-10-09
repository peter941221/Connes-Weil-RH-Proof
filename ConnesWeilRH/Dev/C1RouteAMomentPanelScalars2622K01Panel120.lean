import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P120 : ℚ := ((-28495941949274863182230316965461388337750523541947271 : ℚ) / 862985317394658642081892611427637234213827746201600)

def momentPanelGrowth2622K01P120 : ℚ := ((223032886637976866992845315840989829967054753747232411 : ℚ) / 971759681943357833060026416074351535957046690263859200)

theorem momentPanelPhase_owner2622K01P120 :
    (momentPanelPhase2622K01P120 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (61 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P120 :
    (momentPanelGrowth2622K01P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P120Input : RatPair2542 := (momentPanelPhase2622K01P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P120Expected : RatState2542 :=
  ((((4876193132300963293689548960469624181662290081563273457478248427865182099309266009 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((12363007615685806674849033127176749 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P120_replay :
    compactExp2620 momentScalarAmp2622K01P120Input 20 = momentScalarAmp2622K01P120Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622K01P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P120]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P120 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P120_replay] at h
  simpa only [momentPanelPhase_owner2622K01P120] using h

theorem momentScalarAmp2622K01P120_radius_le :
    (momentScalarAmp2622K01P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P120Expected]

def momentScalarGrow2622K01P120Input : RatPair2542 := (momentPanelGrowth2622K01P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P120Expected : RatState2542 :=
  ((((2687048285175257553068909731870447352354766912552827575270119146170767332425065971246692369699703 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((425779703247543564912794105461324811461288966001 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P120_replay :
    compactExp2620 momentScalarGrow2622K01P120Input 20 = momentScalarGrow2622K01P120Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P120_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P120] using h

theorem momentScalarGrow2622K01P120_radius_le :
    (momentScalarGrow2622K01P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P120Expected]

end ConnesWeilRH.Dev
