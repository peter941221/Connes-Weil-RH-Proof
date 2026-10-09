import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P030 : ℚ := ((-35808599063265629200895622278752653025 : ℚ) / 698769575665007349445830701305823232)

def momentPanelGrowth2622K07P030 : ℚ := ((38927714374939793992421619157275 : ℚ) / 40564819207303340847894502572032)

theorem momentPanelPhase_owner2622K07P030 :
    (momentPanelPhase2622K07P030 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P030 :
    (momentPanelGrowth2622K07P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P030Input : RatPair2542 := (momentPanelPhase2622K07P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P030Expected : RatState2542 :=
  ((((59299812925221540006621746634291356053047370981485089751241382939596910453 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((152768086159477030424742727 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P030_replay :
    compactExp2620 momentScalarAmp2622K07P030Input 20 = momentScalarAmp2622K07P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K07P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P030_replay] at h
  simpa only [momentPanelPhase_owner2622K07P030] using h

theorem momentScalarAmp2622K07P030_radius_le :
    (momentScalarAmp2622K07P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P030Expected]

def momentScalarGrow2622K07P030Input : RatPair2542 := (momentPanelGrowth2622K07P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P030Expected : RatState2542 :=
  ((((2788277219870464197836308988819711330849873968340160339818645381317892889897604899909616668975137 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((883639514147843385738226076481305698020965562695 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P030_replay :
    compactExp2620 momentScalarGrow2622K07P030Input 20 = momentScalarGrow2622K07P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P030] using h

theorem momentScalarGrow2622K07P030_radius_le :
    (momentScalarGrow2622K07P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P030Expected]

end ConnesWeilRH.Dev
