import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P147 : ℚ := ((-802458917128555118348106772516725599891958173474803 : ℚ) / 20381097051841107101512323643738790547545621790720)

def momentPanelGrowth2622K04P147 : ℚ := ((115875370908398932583769202051992409900122471425490029 : ℚ) / 130939556897615065579966012209414197448621408701644800)

theorem momentPanelPhase_owner2622K04P147 :
    (momentPanelPhase2622K04P147 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P147 :
    (momentPanelGrowth2622K04P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P147Input : RatPair2542 := (momentPanelPhase2622K04P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P147Expected : RatState2542 :=
  ((((8496111380903238245395564743767749430212159829115770960366871713853426031964117 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((336578322243995939631636960547 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K04P147_replay :
    compactExp2620 momentScalarAmp2622K04P147Input 20 = momentScalarAmp2622K04P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K04P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P147_replay] at h
  simpa only [momentPanelPhase_owner2622K04P147] using h

theorem momentScalarAmp2622K04P147_radius_le :
    (momentScalarAmp2622K04P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P147Expected]

def momentScalarGrow2622K04P147Input : RatPair2542 := (momentPanelGrowth2622K04P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P147Expected : RatState2542 :=
  ((((5175220687724696829164227145325706588879684594328237728263500711079442163159969666866593345788999 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((410022879652379866419670742070361965122623197455 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K04P147_replay :
    compactExp2620 momentScalarGrow2622K04P147Input 20 = momentScalarGrow2622K04P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P147] using h

theorem momentScalarGrow2622K04P147_radius_le :
    (momentScalarGrow2622K04P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P147Expected]

end ConnesWeilRH.Dev
