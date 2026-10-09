import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K26
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K26P122 : ℚ := ((-6392973838888716750077827804129466831 : ℚ) / 193494187618836935844456777268592640)

def momentPanelGrowth2622K26P122 : ℚ := ((21326790327941182259714339577017031949849 : ℚ) / 80527170733860292660099597189226745036800)

theorem momentPanelPhase_owner2622K26P122 :
    (momentPanelPhase2622K26P122 : ℝ) = momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K26P122 :
    (momentPanelGrowth2622K26P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K26P122Input : RatPair2542 := (momentPanelPhase2622K26P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K26P122Expected : RatState2542 :=
  ((((9564786746581965401394962419474261416009162800568023783464053497948453256750466793 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6062594854887220174282123140276713 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K26P122_replay :
    compactExp2620 momentScalarAmp2622K26P122Input 20 = momentScalarAmp2622K26P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K26P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K26P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K26P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K26P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K26P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K26P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K26P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K26P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K26P122_replay] at h
  simpa only [momentPanelPhase_owner2622K26P122] using h

theorem momentScalarAmp2622K26P122_radius_le :
    (momentScalarAmp2622K26P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarAmp2622K26P122Expected]

def momentScalarGrow2622K26P122Input : RatPair2542 := (momentPanelGrowth2622K26P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K26P122Expected : RatState2542 :=
  ((((1391832680185506305639761978902559535783836397551006248812598954387560338999600649806032408488119 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((441089271707319905905438816012756914125728520507 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K26P122_replay :
    compactExp2620 momentScalarGrow2622K26P122Input 20 = momentScalarGrow2622K26P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K26P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K26P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K26P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K26P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K26P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K26P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K26P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K26P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K26P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K26P122] using h

theorem momentScalarGrow2622K26P122_radius_le :
    (momentScalarGrow2622K26P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarGrow2622K26P122Expected]

end ConnesWeilRH.Dev
