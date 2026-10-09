import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P144 : ℚ := ((-18978343 : ℚ) / 468650)

def momentPanelGrowth2622K06P144 : ℚ := ((465947 : ℚ) / 648675)

theorem momentPanelPhase_owner2622K06P144 :
    (momentPanelPhase2622K06P144 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (109 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P144 :
    (momentPanelGrowth2622K06P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P144Input : RatPair2542 := (momentPanelPhase2622K06P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P144Expected : RatState2542 :=
  ((((5527246076831787167264235471427272293718811144578939811949638790295781506360513 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3503444911978676087267135278033 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P144_replay :
    compactExp2620 momentScalarAmp2622K06P144Input 20 = momentScalarAmp2622K06P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K06P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P144_replay] at h
  simpa only [momentPanelPhase_owner2622K06P144] using h

theorem momentScalarAmp2622K06P144_radius_le :
    (momentScalarAmp2622K06P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P144Expected]

def momentScalarGrow2622K06P144Input : RatPair2542 := (momentPanelGrowth2622K06P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P144Expected : RatState2542 :=
  ((((547601792189996170301319080588876475081490917664361973245565081306071345542380248749919910665921 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((5553338120242378594567567604906096665327964243121 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P144_replay :
    compactExp2620 momentScalarGrow2622K06P144Input 20 = momentScalarGrow2622K06P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P144] using h

theorem momentScalarGrow2622K06P144_radius_le :
    (momentScalarGrow2622K06P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P144Expected]

end ConnesWeilRH.Dev
