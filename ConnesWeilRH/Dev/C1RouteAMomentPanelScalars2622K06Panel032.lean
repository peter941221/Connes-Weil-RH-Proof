import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P032 : ℚ := ((-168211 : ℚ) / 3570)

def momentPanelGrowth2622K06P032 : ℚ := ((19042427 : ℚ) / 22935675)

theorem momentPanelPhase_owner2622K06P032 :
    (momentPanelPhase2622K06P032 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P032, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P032 :
    (momentPanelGrowth2622K06P032 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P032, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P032Input : RatPair2542 := (momentPanelPhase2622K06P032 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P032Expected : RatState2542 :=
  ((((459645339261487940795716047873359094435177632082189426600646866850860987343 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((4662775911013325968945641325 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P032_replay :
    compactExp2620 momentScalarAmp2622K06P032Input 20 = momentScalarAmp2622K06P032Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P032_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 40) 0) -
      (momentScalarAmp2622K06P032Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P032]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P032 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P032 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P032Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P032_replay] at h
  simpa only [momentPanelPhase_owner2622K06P032] using h

theorem momentScalarAmp2622K06P032_radius_le :
    (momentScalarAmp2622K06P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P032Expected]

def momentScalarGrow2622K06P032Input : RatPair2542 := (momentPanelGrowth2622K06P032 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P032Expected : RatState2542 :=
  ((((2449870785744047993425872669436103564161918336712182597363507523204826661168553346526393978665145 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6211155426117792713761979437632402225810960927649 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P032_replay :
    compactExp2620 momentScalarGrow2622K06P032Input 20 = momentScalarGrow2622K06P032Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P032_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P032Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P032]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P032 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P032 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P032Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P032_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P032] using h

theorem momentScalarGrow2622K06P032_radius_le :
    (momentScalarGrow2622K06P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P032Expected]

end ConnesWeilRH.Dev
