import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P065 : ℚ := ((-28585756545782425274388343139798269946713954436625941 : ℚ) / 894384766634189759465174902755526127214248171929600)

def momentPanelGrowth2622K01P065 : ℚ := ((92340470852044148772945751644966849940260528031 : ℚ) / 535217884764734955396857238543560676143529984000)

theorem momentPanelPhase_owner2622K01P065 :
    (momentPanelPhase2622K01P065 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-49 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P065, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P065 :
    (momentPanelGrowth2622K01P065 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P065, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P065Input : RatPair2542 := (momentPanelPhase2622K01P065 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P065Expected : RatState2542 :=
  ((((28116085399460886958808764890651615700208562282091163795405059824699256573921393435 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2227653682923258240294570050592355 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K01P065_replay :
    compactExp2620 momentScalarAmp2622K01P065Input 20 = momentScalarAmp2622K01P065Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P065_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-49 / 200) 0) -
      (momentScalarAmp2622K01P065Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P065]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P065 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P065 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P065Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P065_replay] at h
  simpa only [momentPanelPhase_owner2622K01P065] using h

theorem momentScalarAmp2622K01P065_radius_le :
    (momentScalarAmp2622K01P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P065Expected]

def momentScalarGrow2622K01P065Input : RatPair2542 := (momentPanelGrowth2622K01P065 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P065Expected : RatState2542 :=
  ((((1269103083950826282742417746293754143745211098260203314558190613539736467476123465807740913281319 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3217558042838595621964013057507378828527741952131 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P065_replay :
    compactExp2620 momentScalarGrow2622K01P065Input 20 = momentScalarGrow2622K01P065Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P065_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P065Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P065]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P065 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P065 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P065Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P065_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P065] using h

theorem momentScalarGrow2622K01P065_radius_le :
    (momentScalarGrow2622K01P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P065Expected]

end ConnesWeilRH.Dev
