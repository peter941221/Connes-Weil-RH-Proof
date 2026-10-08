import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P171 : ℚ := ((-104316524878608734402074095297542897608180453439743223 : ℚ) / 1277957584048916477499589257045077945117111327129600)

def momentPanelGrowth2622K04P171 : ℚ := ((149314883047747334768242476706733963389393338276316349 : ℚ) / 31911402986904745192617898505130426905840916942028800)

theorem momentPanelPhase_owner2622K04P171 :
    (momentPanelPhase2622K04P171 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (163 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P171 :
    (momentPanelGrowth2622K04P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P171Input : RatPair2542 := (momentPanelPhase2622K04P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P171Expected : RatState2542 :=
  ((((7572014804745322222485344700774120717580851487794764898406439 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639238857774877099 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P171_replay :
    compactExp2620 momentScalarAmp2622K04P171Input 20 = momentScalarAmp2622K04P171Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622K04P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P171]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P171 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P171_replay] at h
  simpa only [momentPanelPhase_owner2622K04P171] using h

theorem momentScalarAmp2622K04P171_radius_le :
    (momentScalarAmp2622K04P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P171Expected]

def momentScalarGrow2622K04P171Input : RatPair2542 := (momentPanelGrowth2622K04P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P171Expected : RatState2542 :=
  ((((229975691783501504240070971992167450298503441703399713163749395977875921339042940134073596078846931 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18220470177844797064307920826439775794059636600441 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K04P171_replay :
    compactExp2620 momentScalarGrow2622K04P171Input 20 = momentScalarGrow2622K04P171Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P171_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P171] using h

theorem momentScalarGrow2622K04P171_radius_le :
    (momentScalarGrow2622K04P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P171Expected]

end ConnesWeilRH.Dev
