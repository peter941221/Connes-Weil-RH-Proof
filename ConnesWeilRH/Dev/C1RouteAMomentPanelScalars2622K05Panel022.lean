import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P022 : ℚ := ((-19807671314149191931863219302388350013 : ℚ) / 353319575295612098785161117402398720)

def momentPanelGrowth2622K05P022 : ℚ := ((212553563106316130074963510645740083 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K05P022 :
    (momentPanelPhase2622K05P022 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P022 :
    (momentPanelGrowth2622K05P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P022Input : RatPair2542 := (momentPanelPhase2622K05P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P022Expected : RatState2542 :=
  ((((480078267350707434560826712164452123558175369006655686911912605947651461 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3635059722486406879039009 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P022_replay :
    compactExp2620 momentScalarAmp2622K05P022Input 20 = momentScalarAmp2622K05P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K05P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P022_replay] at h
  simpa only [momentPanelPhase_owner2622K05P022] using h

theorem momentScalarAmp2622K05P022_radius_le :
    (momentScalarAmp2622K05P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P022Expected]

def momentScalarGrow2622K05P022Input : RatPair2542 := (momentPanelGrowth2622K05P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P022Expected : RatState2542 :=
  ((((4444161279745551517150160827602780580694973613651908873077192029152504436069737869994903719541239 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5633636053394211485615903645288235428067485707429 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P022_replay :
    compactExp2620 momentScalarGrow2622K05P022Input 20 = momentScalarGrow2622K05P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P022] using h

theorem momentScalarGrow2622K05P022_radius_le :
    (momentScalarGrow2622K05P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P022Expected]

end ConnesWeilRH.Dev
