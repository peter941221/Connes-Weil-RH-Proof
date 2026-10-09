import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P017 : ℚ := ((-1418219102652268998665989262955385375 : ℚ) / 20525798518895490469034618301448192)

def momentPanelGrowth2622K07P017 : ℚ := ((616064906805321250020066798134449638025 : ℚ) / 295017667195457750241502199897238011904)

theorem momentPanelPhase_owner2622K07P017 :
    (momentPanelPhase2622K07P017 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P017 :
    (momentPanelGrowth2622K07P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P017Input : RatPair2542 := (momentPanelPhase2622K07P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P017Expected : RatState2542 :=
  ((((525040729756057636558513153814736150316821274342158859935863868655 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208927150838740294574509 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P017_replay :
    compactExp2620 momentScalarAmp2622K07P017Input 20 = momentScalarAmp2622K07P017Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622K07P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P017]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P017 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P017_replay] at h
  simpa only [momentPanelPhase_owner2622K07P017] using h

theorem momentScalarAmp2622K07P017_radius_le :
    (momentScalarAmp2622K07P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P017Expected]

def momentScalarGrow2622K07P017Input : RatPair2542 := (momentPanelGrowth2622K07P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P017Expected : RatState2542 :=
  ((((2154842994983228281969607451471910484221791884020698182064347660892957990680779464153406303984669 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((21852660608465913910827680283740071642873557917719 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P017_replay :
    compactExp2620 momentScalarGrow2622K07P017Input 20 = momentScalarGrow2622K07P017Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P017_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P017] using h

theorem momentScalarGrow2622K07P017_radius_le :
    (momentScalarGrow2622K07P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P017Expected]

end ConnesWeilRH.Dev
