import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P109 : ℚ := ((-85535154463990564857651724425537943019869308911118087 : ℚ) / 2745953198381631513162089290922356167643585367244800)

def momentPanelGrowth2622K01P109 : ℚ := ((14137289452854182740502913840445058183590708819 : ℚ) / 107043576952946991079371447708712135228705996800)

theorem momentPanelPhase_owner2622K01P109 :
    (momentPanelPhase2622K01P109 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (39 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P109, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P109 :
    (momentPanelGrowth2622K01P109 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P109, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P109Input : RatPair2542 := (momentPanelPhase2622K01P109 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P109Expected : RatState2542 :=
  ((((63318286821492947648285691223293674537304573635246415392997889476161081142048197511 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((80267848739160055802796517269344491 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P109_replay :
    compactExp2620 momentScalarAmp2622K01P109Input 20 = momentScalarAmp2622K01P109Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P109_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (39 / 200) 0) -
      (momentScalarAmp2622K01P109Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P109]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P109 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P109 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P109Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P109_replay] at h
  simpa only [momentPanelPhase_owner2622K01P109] using h

theorem momentScalarAmp2622K01P109_radius_le :
    (momentScalarAmp2622K01P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P109Expected]

def momentScalarGrow2622K01P109Input : RatPair2542 := (momentPanelGrowth2622K01P109 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P109Expected : RatState2542 :=
  ((((304695525939344072861192059116630498517621004137993602764762146535995978162160731347444938887973 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((193123708847582750044550999612232432532692704947 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K01P109_replay :
    compactExp2620 momentScalarGrow2622K01P109Input 20 = momentScalarGrow2622K01P109Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P109_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P109Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P109]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P109 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P109 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P109Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P109_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P109] using h

theorem momentScalarGrow2622K01P109_radius_le :
    (momentScalarGrow2622K01P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P109Expected]

end ConnesWeilRH.Dev
