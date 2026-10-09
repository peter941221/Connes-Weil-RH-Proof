import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P089 : ℚ := ((-73078687203515321108062974226590085523412485412170525 : ℚ) / 2435775166316616076051216234325775187634068574437376)

def momentPanelGrowth2622K03P089 : ℚ := ((27280535607851148201361213400541481111984558613329475 : ℚ) / 3044186149205110647768902662055391854614232402139021312)

theorem momentPanelPhase_owner2622K03P089 :
    (momentPanelPhase2622K03P089 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P089 :
    (momentPanelGrowth2622K03P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P089Input : RatPair2542 := (momentPanelPhase2622K03P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P089Expected : RatState2542 :=
  ((((6232260855454861304687594546719753873951718101435831072682674025913039826732950199 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((252817768465296664111632200534147763 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P089_replay :
    compactExp2620 momentScalarAmp2622K03P089Input 20 = momentScalarAmp2622K03P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K03P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P089_replay] at h
  simpa only [momentPanelPhase_owner2622K03P089] using h

theorem momentScalarAmp2622K03P089_radius_le :
    (momentScalarAmp2622K03P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P089Expected]

def momentScalarGrow2622K03P089Input : RatPair2542 := (momentPanelGrowth2622K03P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P089Expected : RatState2542 :=
  ((((1077607376477611355392683240869745697052795206884336187687822476733515534906723080607625217552299 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1366029625927614740491103713788525016625910791645 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P089_replay :
    compactExp2620 momentScalarGrow2622K03P089Input 20 = momentScalarGrow2622K03P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P089] using h

theorem momentScalarGrow2622K03P089_radius_le :
    (momentScalarGrow2622K03P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P089Expected]

end ConnesWeilRH.Dev
