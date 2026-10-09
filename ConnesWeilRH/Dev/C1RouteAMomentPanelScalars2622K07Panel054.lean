import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P054 : ℚ := ((-35161503314205807140284243626616330225 : ℚ) / 945403676445411661801029276943777792)

def momentPanelGrowth2622K07P054 : ℚ := ((4288925025448050101997092600055675 : ℚ) / 11723232750910665505041511243317248)

theorem momentPanelPhase_owner2622K07P054 :
    (momentPanelPhase2622K07P054 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P054 :
    (momentPanelGrowth2622K07P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P054Input : RatPair2542 := (momentPanelPhase2622K07P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P054Expected : RatState2542 :=
  ((((37604115903804935872769708451196273513766592146064315779445215712902754228388329 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((190682286013962494625065246707571 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P054_replay :
    compactExp2620 momentScalarAmp2622K07P054Input 20 = momentScalarAmp2622K07P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K07P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P054_replay] at h
  simpa only [momentPanelPhase_owner2622K07P054] using h

theorem momentScalarAmp2622K07P054_radius_le :
    (momentScalarAmp2622K07P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P054Expected]

def momentScalarGrow2622K07P054Input : RatPair2542 := (momentPanelGrowth2622K07P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P054Expected : RatState2542 :=
  ((((384941321367514187133308363139463924681009395680841052893566763553171008351208270372106678214685 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3903767414648150620207167633241617540946766663075 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P054_replay :
    compactExp2620 momentScalarGrow2622K07P054Input 20 = momentScalarGrow2622K07P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P054] using h

theorem momentScalarGrow2622K07P054_radius_le :
    (momentScalarGrow2622K07P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P054Expected]

end ConnesWeilRH.Dev
