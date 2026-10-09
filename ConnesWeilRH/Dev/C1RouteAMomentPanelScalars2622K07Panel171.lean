import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P171 : ℚ := ((-30061890743342094653003764141725862675 : ℚ) / 363217391182194113952047376029974528)

def momentPanelGrowth2622K07P171 : ℚ := ((42311196334001018886187967648151591025 : ℚ) / 9069766232103332070158188146572918784)

theorem momentPanelPhase_owner2622K07P171 :
    (momentPanelPhase2622K07P171 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (163 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P171 :
    (momentPanelGrowth2622K07P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P171Input : RatPair2542 := (momentPanelPhase2622K07P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P171Expected : RatState2542 :=
  ((((606614334824409276824540668892197853369873606541527634486565 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639232334497463617 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P171_replay :
    compactExp2620 momentScalarAmp2622K07P171Input 20 = momentScalarAmp2622K07P171Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622K07P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P171]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P171 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P171_replay] at h
  simpa only [momentPanelPhase_owner2622K07P171] using h

theorem momentScalarAmp2622K07P171_radius_le :
    (momentScalarAmp2622K07P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P171Expected]

def momentScalarGrow2622K07P171Input : RatPair2542 := (momentPanelGrowth2622K07P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P171Expected : RatState2542 :=
  ((((113393368968581312580755227665101007741965819733050608271192750993907946086402689926223117631462363 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((143742532727548400027804795120936156725713342102143 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P171_replay :
    compactExp2620 momentScalarGrow2622K07P171Input 20 = momentScalarGrow2622K07P171Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P171_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P171] using h

theorem momentScalarGrow2622K07P171_radius_le :
    (momentScalarGrow2622K07P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P171Expected]

end ConnesWeilRH.Dev
