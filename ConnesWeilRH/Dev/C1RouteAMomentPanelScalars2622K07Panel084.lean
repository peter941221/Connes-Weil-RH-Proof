import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P084 : ℚ := ((-32930741721594020769096118803168404725 : ℚ) / 1078456283445366619782123245380042752)

def momentPanelGrowth2622K07P084 : ℚ := ((29448980516030801956387416098064567075 : ℚ) / 251707988931673021531794067914166894592)

theorem momentPanelPhase_owner2622K07P084 :
    (momentPanelPhase2622K07P084 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P084 :
    (momentPanelGrowth2622K07P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P084Input : RatPair2542 := (momentPanelPhase2622K07P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P084Expected : RatState2542 :=
  ((((58526796805890414042780290177458530486243425667050840298736578378781684350563248677 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((148387379257280930172856636527683809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P084_replay :
    compactExp2620 momentScalarAmp2622K07P084Input 20 = momentScalarAmp2622K07P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K07P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P084_replay] at h
  simpa only [momentPanelPhase_owner2622K07P084] using h

theorem momentScalarAmp2622K07P084_radius_le :
    (momentScalarAmp2622K07P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P084Expected]

def momentScalarGrow2622K07P084Input : RatPair2542 := (momentPanelGrowth2622K07P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P084Expected : RatState2542 :=
  ((((1200548190170255397427549694604432969376654931087813052186865579634399492464419620936662386202291 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1521875464066450133010975290721307686726965917313 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P084_replay :
    compactExp2620 momentScalarGrow2622K07P084Input 20 = momentScalarGrow2622K07P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P084] using h

theorem momentScalarGrow2622K07P084_radius_le :
    (momentScalarGrow2622K07P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P084Expected]

end ConnesWeilRH.Dev
