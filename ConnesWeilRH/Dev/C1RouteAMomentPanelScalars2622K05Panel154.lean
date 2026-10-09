import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P154 : ℚ := ((-2390764850497962929981805965514689964321 : ℚ) / 47377680593169936943298384279004774400)

def momentPanelGrowth2622K05P154 : ℚ := ((21348260515561716725300740837911190043 : ℚ) / 18038160981007613091537487931218329600)

theorem momentPanelPhase_owner2622K05P154 :
    (momentPanelPhase2622K05P154 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (129 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P154 :
    (momentPanelGrowth2622K05P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P154Input : RatPair2542 := (momentPanelPhase2622K05P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P154Expected : RatState2542 :=
  ((((129798823833799612542679484422127652600120703526851481278038475736402635555 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((41439100319953025352954441 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P154_replay :
    compactExp2620 momentScalarAmp2622K05P154Input 20 = momentScalarAmp2622K05P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K05P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P154_replay] at h
  simpa only [momentPanelPhase_owner2622K05P154] using h

theorem momentScalarAmp2622K05P154_radius_le :
    (momentScalarAmp2622K05P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P154Expected]

def momentScalarGrow2622K05P154Input : RatPair2542 := (momentPanelGrowth2622K05P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P154Expected : RatState2542 :=
  ((((1743927699327505528930570249610014374668759228727571195074096329203392467730693968858191244836385 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4421376999297516756695203839831274764702322710005 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P154_replay :
    compactExp2620 momentScalarGrow2622K05P154Input 20 = momentScalarGrow2622K05P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P154] using h

theorem momentScalarGrow2622K05P154_radius_le :
    (momentScalarGrow2622K05P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P154Expected]

end ConnesWeilRH.Dev
