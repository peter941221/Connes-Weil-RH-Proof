import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P174 : ℚ := ((-801175035076850280660872505830587312507 : ℚ) / 7733682781872381932651086915357900800)

def momentPanelGrowth2622K28P174 : ℚ := ((27648584469640229468133944177392330483 : ℚ) / 4164992812109870521557568051583385600)

theorem momentPanelPhase_owner2622K28P174 :
    (momentPanelPhase2622K28P174 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P174 :
    (momentPanelGrowth2622K28P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P174Input : RatPair2542 := (momentPanelPhase2622K28P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P174Expected : RatState2542 :=
  ((((2180859766353750134010464044248249806981613180517229 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231454903657293676909 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K28P174_replay :
    compactExp2620 momentScalarAmp2622K28P174Input 20 = momentScalarAmp2622K28P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K28P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P174_replay] at h
  simpa only [momentPanelPhase_owner2622K28P174] using h

theorem momentScalarAmp2622K28P174_radius_le :
    (momentScalarAmp2622K28P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P174Expected]

def momentScalarGrow2622K28P174Input : RatPair2542 := (momentPanelGrowth2622K28P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P174Expected : RatState2542 :=
  ((((815750645252163344473079381769857220208613863752197680435407325956912322294627125433274587413224997 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2068160497024850539846393009686574282556435330670837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K28P174_replay :
    compactExp2620 momentScalarGrow2622K28P174Input 20 = momentScalarGrow2622K28P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P174] using h

theorem momentScalarGrow2622K28P174_radius_le :
    (momentScalarGrow2622K28P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P174Expected]

end ConnesWeilRH.Dev
