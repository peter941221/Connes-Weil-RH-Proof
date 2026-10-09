import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P174 : ℚ := ((-802074245841264147153759443058427671667 : ℚ) / 7733682781872381932651086915357900800)

def momentPanelGrowth2622K05P174 : ℚ := ((27642853439530766280555034512706212523 : ℚ) / 4164992812109870521557568051583385600)

theorem momentPanelPhase_owner2622K05P174 :
    (momentPanelPhase2622K05P174 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P174 :
    (momentPanelGrowth2622K05P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P174Input : RatPair2542 := (momentPanelPhase2622K05P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P174Expected : RatState2542 :=
  ((((1941473434824559732496525886716247472652228249788187 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((151115727451828646838435 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K05P174_replay :
    compactExp2620 momentScalarAmp2622K05P174Input 20 = momentScalarAmp2622K05P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K05P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P174_replay] at h
  simpa only [momentPanelPhase_owner2622K05P174] using h

theorem momentScalarAmp2622K05P174_radius_le :
    (momentScalarAmp2622K05P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P174Expected]

def momentScalarGrow2622K05P174Input : RatPair2542 := (momentPanelGrowth2622K05P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P174Expected : RatState2542 :=
  ((((407314472135777248105910908092586914597485076930417437813947023615966854287496654438038361122352563 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2065316667896176966405395897780110498640097491062031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P174_replay :
    compactExp2620 momentScalarGrow2622K05P174Input 20 = momentScalarGrow2622K05P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P174] using h

theorem momentScalarGrow2622K05P174_radius_le :
    (momentScalarGrow2622K05P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P174Expected]

end ConnesWeilRH.Dev
