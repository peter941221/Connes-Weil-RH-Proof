import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P094 : ℚ := ((-219128096194504423441413736186174862883018246095061825 : ℚ) / 7292710482576539198971611854650162732705646397882368)

def momentPanelGrowth2622K03P094 : ℚ := ((160499853750062258056827074339393866119328382347075 : ℚ) / 4847344211764939072519683938609686937755085766131712)

theorem momentPanelPhase_owner2622K03P094 :
    (momentPanelPhase2622K03P094 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P094 :
    (momentPanelGrowth2622K03P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P094Input : RatPair2542 := (momentPanelPhase2622K03P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P094Expected : RatState2542 :=
  ((((190595507053689541419793833018666296682016659602442875720229403593776698017654741263 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((241615432450610925418057861411830891 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P094_replay :
    compactExp2620 momentScalarAmp2622K03P094Input 20 = momentScalarAmp2622K03P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K03P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P094_replay] at h
  simpa only [momentPanelPhase_owner2622K03P094] using h

theorem momentScalarAmp2622K03P094_radius_le :
    (momentScalarAmp2622K03P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P094Expected]

def momentScalarGrow2622K03P094Input : RatPair2542 := (momentPanelGrowth2622K03P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P094Expected : RatState2542 :=
  ((((2207895360325648319613607969218104544817348416498864655590214289206101655576103763608478002984485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((349854973797370680446106936302079687460317492403 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P094_replay :
    compactExp2620 momentScalarGrow2622K03P094Input 20 = momentScalarGrow2622K03P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P094] using h

theorem momentScalarGrow2622K03P094_radius_le :
    (momentScalarGrow2622K03P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P094Expected]

end ConnesWeilRH.Dev
