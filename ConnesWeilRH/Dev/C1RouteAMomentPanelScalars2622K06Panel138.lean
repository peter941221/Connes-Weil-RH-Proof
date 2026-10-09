import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P138 : ℚ := ((-19010891 : ℚ) / 509850)

def momentPanelGrowth2622K06P138 : ℚ := ((264248267 : ℚ) / 481206675)

theorem momentPanelPhase_owner2622K06P138 :
    (momentPanelPhase2622K06P138 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P138 :
    (momentPanelGrowth2622K06P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P138Input : RatPair2542 := (momentPanelPhase2622K06P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P138Expected : RatState2542 :=
  ((((17095158430915562309852673027849941327676207115581899970537821446316098451505513 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((173371670149356980108094310524569 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P138_replay :
    compactExp2620 momentScalarAmp2622K06P138Input 20 = momentScalarAmp2622K06P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K06P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P138_replay] at h
  simpa only [momentPanelPhase_owner2622K06P138] using h

theorem momentScalarAmp2622K06P138_radius_le :
    (momentScalarAmp2622K06P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P138Expected]

def momentScalarGrow2622K06P138Input : RatPair2542 := (momentPanelGrowth2622K06P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P138Expected : RatState2542 :=
  ((((3699011405980453631135179163537171095289264585930595978287863837893705803409265852174417596090269 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4689051573396445870016477961919605742033045696605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P138_replay :
    compactExp2620 momentScalarGrow2622K06P138Input 20 = momentScalarGrow2622K06P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P138] using h

theorem momentScalarGrow2622K06P138_radius_le :
    (momentScalarGrow2622K06P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P138Expected]

end ConnesWeilRH.Dev
