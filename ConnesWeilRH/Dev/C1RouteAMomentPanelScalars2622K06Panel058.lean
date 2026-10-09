import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P058 : ℚ := ((-62269953 : ℚ) / 1801550)

def momentPanelGrowth2622K06P058 : ℚ := ((729907 : ℚ) / 2622675)

theorem momentPanelPhase_owner2622K06P058 :
    (momentPanelPhase2622K06P058 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-63 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P058 :
    (momentPanelGrowth2622K06P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P058Input : RatPair2542 := (momentPanelPhase2622K06P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P058Expected : RatState2542 :=
  ((((260177647814759583840223778048835512034171979202345898634092169564704944908011147 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1319300894839095466095411632303907 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P058_replay :
    compactExp2620 momentScalarAmp2622K06P058Input 20 = momentScalarAmp2622K06P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K06P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P058_replay] at h
  simpa only [momentPanelPhase_owner2622K06P058] using h

theorem momentScalarAmp2622K06P058_radius_le :
    (momentScalarAmp2622K06P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P058Expected]

def momentScalarGrow2622K06P058Input : RatPair2542 := (momentPanelGrowth2622K06P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P058Expected : RatState2542 :=
  ((((1410702744510626740039310070954456007430599768296884040917458932349058443002293419554497660481907 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3576555412378513363637636560391382718552150083397 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P058_replay :
    compactExp2620 momentScalarGrow2622K06P058Input 20 = momentScalarGrow2622K06P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P058] using h

theorem momentScalarGrow2622K06P058_radius_le :
    (momentScalarGrow2622K06P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P058Expected]

end ConnesWeilRH.Dev
