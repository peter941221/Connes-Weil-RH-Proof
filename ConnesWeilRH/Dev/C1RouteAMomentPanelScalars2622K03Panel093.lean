import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P093 : ℚ := ((-73049874793341608688924392136111020258903302956709925 : ℚ) / 2432852163041954270214808864660342621594756709351424)

def momentPanelGrowth2622K03P093 : ℚ := ((1252133625626585557775610148493200501777693231475 : ℚ) / 46311333132922986220579263136697218185347362455552)

theorem momentPanelPhase_owner2622K03P093 :
    (momentPanelPhase2622K03P093 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P093 :
    (momentPanelGrowth2622K03P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P093Input : RatPair2542 := (momentPanelPhase2622K03P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P093Expected : RatState2542 :=
  ((((194663279211746364980515694163339198632833234202181088300834806352584953321402701537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((61693022265870449632611403023282355 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P093_replay :
    compactExp2620 momentScalarAmp2622K03P093Input 20 = momentScalarAmp2622K03P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K03P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P093_replay] at h
  simpa only [momentPanelPhase_owner2622K03P093] using h

theorem momentScalarAmp2622K03P093_radius_le :
    (momentScalarAmp2622K03P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P093Expected]

def momentScalarGrow2622K03P093Input : RatPair2542 := (momentPanelGrowth2622K03P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P093Expected : RatState2542 :=
  ((((2194526172469623957739772415997483859634664249433532991867163415175513560334225926615482289458627 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((347736543502148254877899998551702812429243351933 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P093_replay :
    compactExp2620 momentScalarGrow2622K03P093Input 20 = momentScalarGrow2622K03P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P093] using h

theorem momentScalarGrow2622K03P093_radius_le :
    (momentScalarGrow2622K03P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P093Expected]

end ConnesWeilRH.Dev
