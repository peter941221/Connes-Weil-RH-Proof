import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P038 : ℚ := ((-35756670009308362728949239879832327825 : ℚ) / 794827067547901660573644883396395008)

def momentPanelGrowth2622K07P038 : ℚ := ((29296022483868981685480753210279225 : ℚ) / 43931699201509518138269746285510656)

theorem momentPanelPhase_owner2622K07P038 :
    (momentPanelPhase2622K07P038 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-103 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P038 :
    (momentPanelGrowth2622K07P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P038Input : RatPair2542 := (momentPanelPhase2622K07P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P038Expected : RatState2542 :=
  ((((30979926841563391202383257136578727062313070292656693460977516693151054087067 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((78549233360354310840254077033 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P038_replay :
    compactExp2620 momentScalarAmp2622K07P038Input 20 = momentScalarAmp2622K07P038Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622K07P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P038]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P038 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P038_replay] at h
  simpa only [momentPanelPhase_owner2622K07P038] using h

theorem momentScalarAmp2622K07P038_radius_le :
    (momentScalarAmp2622K07P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P038Expected]

def momentScalarGrow2622K07P038Input : RatPair2542 := (momentPanelGrowth2622K07P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P038Expected : RatState2542 :=
  ((((1040278363536606589347206623614821306975280484166706556863883363890714468304203525613520352970101 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((659354326646786490517928622687643820677701228573 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P038_replay :
    compactExp2620 momentScalarGrow2622K07P038Input 20 = momentScalarGrow2622K07P038Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P038_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P038] using h

theorem momentScalarGrow2622K07P038_radius_le :
    (momentScalarGrow2622K07P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P038Expected]

end ConnesWeilRH.Dev
