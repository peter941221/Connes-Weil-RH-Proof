import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K27
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K27P057 : ℚ := ((-6587768307448352321248413018920773169 : ℚ) / 193494187618836935844456777268592640)

def momentPanelGrowth2622K27P057 : ℚ := ((21326790327941182259714339577017031949849 : ℚ) / 80527170733860292660099597189226745036800)

theorem momentPanelPhase_owner2622K27P057 :
    (momentPanelPhase2622K27P057 : ℝ) = momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-13 / 40) 0 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P057, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K27P057 :
    (momentPanelGrowth2622K27P057 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2))
      (-13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P057, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K27P057Input : RatPair2542 := (momentPanelPhase2622K27P057 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K27P057Expected : RatState2542 :=
  ((((873780522172085916373990724809717216833665071281432301539870429651900259378631039 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4430737475812953048689604544350189 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K27P057_replay :
    compactExp2620 momentScalarAmp2622K27P057Input 20 = momentScalarAmp2622K27P057Expected := by
  decide +kernel

theorem momentScalarAmp2622K27P057_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-13 / 40) 0) -
      (momentScalarAmp2622K27P057Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K27P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K27P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P057]
  have h := compactExp_real_error2620 momentPanelPhase2622K27P057 20 hsmall
  change |Real.exp (momentPanelPhase2622K27P057 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K27P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K27P057Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K27P057_replay] at h
  simpa only [momentPanelPhase_owner2622K27P057] using h

theorem momentScalarAmp2622K27P057_radius_le :
    (momentScalarAmp2622K27P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarAmp2622K27P057Expected]

def momentScalarGrow2622K27P057Input : RatPair2542 := (momentPanelGrowth2622K27P057 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K27P057Expected : RatState2542 :=
  ((((1391832680185506305639761978902559535783836397551006248812598954387560338999600649806032408488119 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((441089271707319905905438816012756914125728520507 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K27P057_replay :
    compactExp2620 momentScalarGrow2622K27P057Input 20 = momentScalarGrow2622K27P057Expected := by
  decide +kernel

theorem momentScalarGrow2622K27P057_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K27P057Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K27P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K27P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P057]
  have h := compactExp_real_error2620 momentPanelGrowth2622K27P057 20 hsmall
  change |Real.exp (momentPanelGrowth2622K27P057 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K27P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K27P057Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K27P057_replay] at h
  simpa only [momentPanelGrowth_owner2622K27P057] using h

theorem momentScalarGrow2622K27P057_radius_le :
    (momentScalarGrow2622K27P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarGrow2622K27P057Expected]

end ConnesWeilRH.Dev
