import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P125 : ℚ := ((-29742207417479538216346960488634869775 : ℚ) / 945403676445411661801029276943777792)

def momentPanelGrowth2622K07P125 : ℚ := ((4288925025448050101997092600055675 : ℚ) / 11723232750910665505041511243317248)

theorem momentPanelPhase_owner2622K07P125 :
    (momentPanelPhase2622K07P125 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (71 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P125 :
    (momentPanelGrowth2622K07P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P125Input : RatPair2542 := (momentPanelPhase2622K07P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P125Expected : RatState2542 :=
  ((((46428272373587714359575501912659694454870601746567474255558417163919053239567266805 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((58856593156921111559747644332807673 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P125_replay :
    compactExp2620 momentScalarAmp2622K07P125Input 20 = momentScalarAmp2622K07P125Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622K07P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P125]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P125 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P125_replay] at h
  simpa only [momentPanelPhase_owner2622K07P125] using h

theorem momentScalarAmp2622K07P125_radius_le :
    (momentScalarAmp2622K07P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P125Expected]

def momentScalarGrow2622K07P125Input : RatPair2542 := (momentPanelGrowth2622K07P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P125Expected : RatState2542 :=
  ((((384941321367514187133308363139463924681009395680841052893566763553171008351208270372106678214685 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3903767414648150620207167633241617540946766663075 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P125_replay :
    compactExp2620 momentScalarGrow2622K07P125Input 20 = momentScalarGrow2622K07P125Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P125_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P125] using h

theorem momentScalarGrow2622K07P125_radius_le :
    (momentScalarGrow2622K07P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P125Expected]

end ConnesWeilRH.Dev
