import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K23
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K23P096 : ℚ := ((-808585392365074907651357703540446945231 : ℚ) / 26928955230768322821874765532443443200)

def momentPanelGrowth2622K23P096 : ℚ := ((1938206988072800339403709851584735210323 : ℚ) / 33473548283650779550665745328194034073600)

theorem momentPanelPhase_owner2622K23P096 :
    (momentPanelPhase2622K23P096 : ℝ) = momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (13 / 200) 0 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P096, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K23P096 :
    (momentPanelGrowth2622K23P096 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2))
      (13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P096, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K23P096Input : RatPair2542 := (momentPanelPhase2622K23P096 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K23P096Expected : RatState2542 :=
  ((((24328485681578012442917941067106815213120527534661192843865526655115307419546098677 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((15420451306341846829006523753201495 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K23P096_replay :
    compactExp2620 momentScalarAmp2622K23P096Input 20 = momentScalarAmp2622K23P096Expected := by
  decide +kernel

theorem momentScalarAmp2622K23P096_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (13 / 200) 0) -
      (momentScalarAmp2622K23P096Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K23P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K23P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P096]
  have h := compactExp_real_error2620 momentPanelPhase2622K23P096 20 hsmall
  change |Real.exp (momentPanelPhase2622K23P096 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K23P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K23P096Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K23P096_replay] at h
  simpa only [momentPanelPhase_owner2622K23P096] using h

theorem momentScalarAmp2622K23P096_radius_le :
    (momentScalarAmp2622K23P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarAmp2622K23P096Expected]

def momentScalarGrow2622K23P096Input : RatPair2542 := (momentPanelGrowth2622K23P096 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K23P096Expected : RatState2542 :=
  ((((2263317136974390509901294860813865918725934139874732056604890227399204263164026378600919774470937 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1434547584380111232004108307035184926223174946833 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K23P096_replay :
    compactExp2620 momentScalarGrow2622K23P096Input 20 = momentScalarGrow2622K23P096Expected := by
  decide +kernel

theorem momentScalarGrow2622K23P096_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K23P096Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K23P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K23P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P096]
  have h := compactExp_real_error2620 momentPanelGrowth2622K23P096 20 hsmall
  change |Real.exp (momentPanelGrowth2622K23P096 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K23P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K23P096Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K23P096_replay] at h
  simpa only [momentPanelGrowth_owner2622K23P096] using h

theorem momentScalarGrow2622K23P096_radius_le :
    (momentScalarGrow2622K23P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarGrow2622K23P096Expected]

end ConnesWeilRH.Dev
