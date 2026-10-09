import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P107 : ℚ := ((-2918110259400775295222665080561154090579850139901625 : ℚ) / 94449543312509601088913132314289790145264640589824)

def momentPanelGrowth2622K03P107 : ℚ := ((63239403572968819976131391037153485505675417335881425 : ℚ) / 534504123902603475684179513963382861423805517944324096)

theorem momentPanelPhase_owner2622K03P107 :
    (momentPanelPhase2622K03P107 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P107 :
    (momentPanelGrowth2622K03P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P107Input : RatPair2542 := (momentPanelPhase2622K03P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P107Expected : RatState2542 :=
  ((((40796163187993497677888717167564324468586799862000929669198142410613836765235935653 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((103433609101604919230434370657791783 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P107_replay :
    compactExp2620 momentScalarAmp2622K03P107Input 20 = momentScalarAmp2622K03P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K03P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P107_replay] at h
  simpa only [momentPanelPhase_owner2622K03P107] using h

theorem momentScalarAmp2622K03P107_radius_le :
    (momentScalarAmp2622K03P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P107Expected]

def momentScalarGrow2622K03P107Input : RatPair2542 := (momentPanelGrowth2622K03P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P107Expected : RatState2542 :=
  ((((601065506394176749077347754507091225265963818491715522372684899566361158632144366553038069303513 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((380970481992421619175859562449487831020280575653 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P107_replay :
    compactExp2620 momentScalarGrow2622K03P107Input 20 = momentScalarGrow2622K03P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P107] using h

theorem momentScalarGrow2622K03P107_radius_le :
    (momentScalarGrow2622K03P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P107Expected]

end ConnesWeilRH.Dev
