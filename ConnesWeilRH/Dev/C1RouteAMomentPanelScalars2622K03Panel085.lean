import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P085 : ℚ := ((-219322395004766452019691713628710043013761516797738175 : ℚ) / 7292710482576539198971611854650162732705646397882368)

def momentPanelGrowth2622K03P085 : ℚ := ((160499853750062258056827074339393866119328382347075 : ℚ) / 4847344211764939072519683938609686937755085766131712)

theorem momentPanelPhase_owner2622K03P085 :
    (momentPanelPhase2622K03P085 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P085, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P085 :
    (momentPanelGrowth2622K03P085 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P085, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P085Input : RatPair2542 := (momentPanelPhase2622K03P085 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P085Expected : RatState2542 :=
  ((((185584543494086958238812863651621510982405574287984058187232087691605808644792706539 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((235263105437103827194426749667742583 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P085_replay :
    compactExp2620 momentScalarAmp2622K03P085Input 20 = momentScalarAmp2622K03P085Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P085_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 200) 0) -
      (momentScalarAmp2622K03P085Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P085]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P085 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P085 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P085Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P085_replay] at h
  simpa only [momentPanelPhase_owner2622K03P085] using h

theorem momentScalarAmp2622K03P085_radius_le :
    (momentScalarAmp2622K03P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P085Expected]

def momentScalarGrow2622K03P085Input : RatPair2542 := (momentPanelGrowth2622K03P085 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P085Expected : RatState2542 :=
  ((((2207895360325648319613607969218104544817348416498864655590214289206101655576103763608478002984485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((349854973797370680446106936302079687460317492403 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P085_replay :
    compactExp2620 momentScalarGrow2622K03P085Input 20 = momentScalarGrow2622K03P085Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P085_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P085Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P085]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P085 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P085 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P085Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P085_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P085] using h

theorem momentScalarGrow2622K03P085_radius_le :
    (momentScalarGrow2622K03P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P085Expected]

end ConnesWeilRH.Dev
