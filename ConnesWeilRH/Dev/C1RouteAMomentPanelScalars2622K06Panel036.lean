import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P036 : ℚ := ((-21018319 : ℚ) / 475850)

def momentPanelGrowth2622K06P036 : ℚ := ((53761441 : ℚ) / 78411025)

theorem momentPanelPhase_owner2622K06P036 :
    (momentPanelPhase2622K06P036 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-107 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P036 :
    (momentPanelGrowth2622K06P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P036Input : RatPair2542 := (momentPanelPhase2622K06P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P036Expected : RatState2542 :=
  ((((70106613771384690660273183764334568393327979569854167563561696412724291842427 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((88875643607027235426052723607 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P036_replay :
    compactExp2620 momentScalarAmp2622K06P036Input 20 = momentScalarAmp2622K06P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K06P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P036_replay] at h
  simpa only [momentPanelPhase_owner2622K06P036] using h

theorem momentScalarAmp2622K06P036_radius_le :
    (momentScalarAmp2622K06P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P036Expected]

def momentScalarGrow2622K06P036Input : RatPair2542 := (momentPanelGrowth2622K06P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P036Expected : RatState2542 :=
  ((((2120003881149388186026532543552921313977538388960163302398319586203388003010833511595432905073485 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5374844870379650208885110288809485559120139176219 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P036_replay :
    compactExp2620 momentScalarGrow2622K06P036Input 20 = momentScalarGrow2622K06P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P036] using h

theorem momentScalarGrow2622K06P036_radius_le :
    (momentScalarGrow2622K06P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P036Expected]

end ConnesWeilRH.Dev
