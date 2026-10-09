import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P098 : ℚ := ((-73014232442329923934375847713237253529841855593410675 : ℚ) / 2418237146668645241032772016333179791398197383921664)

def momentPanelGrowth2622K03P098 : ℚ := ((519861220640258058360554899703301133947431316840856425 : ℚ) / 8987007499553547321682803013675960937915162884462084096)

theorem momentPanelPhase_owner2622K03P098 :
    (momentPanelPhase2622K03P098 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P098 :
    (momentPanelGrowth2622K03P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P098Input : RatPair2542 := (momentPanelPhase2622K03P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P098Expected : RatState2542 :=
  ((((164768350498737727637082954782266076381464847017856121270955365609964166050182817997 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((208874712755742466571558454153896683 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P098_replay :
    compactExp2620 momentScalarAmp2622K03P098Input 20 = momentScalarAmp2622K03P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K03P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P098_replay] at h
  simpa only [momentPanelPhase_owner2622K03P098] using h

theorem momentScalarAmp2622K03P098_radius_le :
    (momentScalarAmp2622K03P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P098Expected]

def momentScalarGrow2622K03P098Input : RatPair2542 := (momentPanelGrowth2622K03P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P098Expected : RatState2542 :=
  ((((565797157164174608548060386742779626709358296179121734049313492183660000770476869685206743777443 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((179308266579907123170616668472870730482923477515 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K03P098_replay :
    compactExp2620 momentScalarGrow2622K03P098Input 20 = momentScalarGrow2622K03P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P098] using h

theorem momentScalarGrow2622K03P098_radius_le :
    (momentScalarGrow2622K03P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P098Expected]

end ConnesWeilRH.Dev
