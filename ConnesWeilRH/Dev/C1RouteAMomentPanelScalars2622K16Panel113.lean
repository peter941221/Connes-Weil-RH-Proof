import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P113 : ℚ := ((-801997092236620818197070384315649995229 : ℚ) / 25549751377720009233046352444994355200)

def momentPanelGrowth2622K16P113 : ℚ := ((62493260386111101327799200547404178849 : ℚ) / 351819691105422057757310218169797836800)

theorem momentPanelPhase_owner2622K16P113 :
    (momentPanelPhase2622K16P113 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (47 / 200) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P113, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P113 :
    (momentPanelGrowth2622K16P113 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P113, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P113Input : RatPair2542 := (momentPanelPhase2622K16P113 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P113Expected : RatState2542 :=
  ((((3112705859854137891131871659724295144633162644715818799989157444017467400484739597 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((63135065177753233778403093597504283 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K16P113_replay :
    compactExp2620 momentScalarAmp2622K16P113Input 20 = momentScalarAmp2622K16P113Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P113_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (47 / 200) 0) -
      (momentScalarAmp2622K16P113Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P113]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P113 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P113 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P113Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P113_replay] at h
  simpa only [momentPanelPhase_owner2622K16P113] using h

theorem momentScalarAmp2622K16P113_radius_le :
    (momentScalarAmp2622K16P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P113Expected]

def momentScalarGrow2622K16P113Input : RatPair2542 := (momentPanelGrowth2622K16P113 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P113Expected : RatState2542 :=
  ((((318897983061460437740642707020105069675752420036413402091586328886429490284748507821668287079805 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1617004604637301036225264646453130324741510626171 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K16P113_replay :
    compactExp2620 momentScalarGrow2622K16P113Input 20 = momentScalarGrow2622K16P113Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P113_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P113Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P113]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P113 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P113 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P113Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P113_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P113] using h

theorem momentScalarGrow2622K16P113_radius_le :
    (momentScalarGrow2622K16P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P113Expected]

end ConnesWeilRH.Dev
