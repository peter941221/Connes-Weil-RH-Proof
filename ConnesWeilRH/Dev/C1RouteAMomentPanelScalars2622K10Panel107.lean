import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P107 : ℚ := ((-6433528533117145958654061558732849589 : ℚ) / 209720115301758272183614578297405440)

def momentPanelGrowth2622K10P107 : ℚ := ((776440025561664267267381220182948991009 : ℚ) / 5934187851137678611881160084122553548800)

theorem momentPanelPhase_owner2622K10P107 :
    (momentPanelPhase2622K10P107 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P107 :
    (momentPanelGrowth2622K10P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P107Input : RatPair2542 := (momentPanelPhase2622K10P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P107Expected : RatState2542 :=
  ((((101592490299553512323499055901234406929673509844132310323144589721593156902997861483 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16098443626643643356924725956024251 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K10P107_replay :
    compactExp2620 momentScalarAmp2622K10P107Input 20 = momentScalarAmp2622K10P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K10P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P107_replay] at h
  simpa only [momentPanelPhase_owner2622K10P107] using h

theorem momentScalarAmp2622K10P107_radius_le :
    (momentScalarAmp2622K10P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P107Expected]

def momentScalarGrow2622K10P107Input : RatPair2542 := (momentPanelGrowth2622K10P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P107Expected : RatState2542 :=
  ((((2434571306957533418970792336734736155776863540361511453020009721240453239889373633113770304628499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3086185393467370314997015398768511395035785216541 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K10P107_replay :
    compactExp2620 momentScalarGrow2622K10P107Input 20 = momentScalarGrow2622K10P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P107] using h

theorem momentScalarGrow2622K10P107_radius_le :
    (momentScalarGrow2622K10P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P107Expected]

end ConnesWeilRH.Dev
