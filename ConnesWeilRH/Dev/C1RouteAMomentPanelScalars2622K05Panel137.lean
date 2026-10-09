import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P137 : ℚ := ((-6378070551474941067734168408372994617 : ℚ) / 167532703326162797701804295622492160)

def momentPanelGrowth2622K05P137 : ℚ := ((117399623346340503192624820840317492129 : ℚ) / 234627928415522706047743000239197388800)

theorem momentPanelPhase_owner2622K05P137 :
    (momentPanelPhase2622K05P137 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P137, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P137 :
    (momentPanelGrowth2622K05P137 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P137, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P137Input : RatPair2542 := (momentPanelPhase2622K05P137 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P137Expected : RatState2542 :=
  ((((31240434965770589251041811990937551934237120346015681375078701071386164809908995 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((79206790394317144434196423010009 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P137_replay :
    compactExp2620 momentScalarAmp2622K05P137Input 20 = momentScalarAmp2622K05P137Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P137_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 40) 0) -
      (momentScalarAmp2622K05P137Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P137]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P137 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P137 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P137Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P137_replay] at h
  simpa only [momentPanelPhase_owner2622K05P137] using h

theorem momentScalarAmp2622K05P137_radius_le :
    (momentScalarAmp2622K05P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P137Expected]

def momentScalarGrow2622K05P137Input : RatPair2542 := (momentPanelGrowth2622K05P137 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P137Expected : RatState2542 :=
  ((((1761466597698025163168682103080183085079121210690108832962518905208701370164056657093129599777729 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2232923124335465665541746773845139651985059525163 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P137_replay :
    compactExp2620 momentScalarGrow2622K05P137Input 20 = momentScalarGrow2622K05P137Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P137_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P137Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P137]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P137 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P137 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P137Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P137_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P137] using h

theorem momentScalarGrow2622K05P137_radius_le :
    (momentScalarGrow2622K05P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P137Expected]

end ConnesWeilRH.Dev
