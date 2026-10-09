import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P070 : ℚ := ((-2455365800736360708175197823627684581609 : ℚ) / 78044683913891262624306628223460966400)

def momentPanelGrowth2622K05P070 : ℚ := ((439074617220331552092462457103267 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K05P070 :
    (momentPanelPhase2622K05P070 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P070 :
    (momentPanelGrowth2622K05P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P070Input : RatPair2542 := (momentPanelPhase2622K05P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P070Expected : RatState2542 :=
  ((((46371248313918659924924201032106515278088365773788739653228343247706523526326630249 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29392152236774112757808501330048719 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P070_replay :
    compactExp2620 momentScalarAmp2622K05P070Input 20 = momentScalarAmp2622K05P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K05P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P070_replay] at h
  simpa only [momentPanelPhase_owner2622K05P070] using h

theorem momentScalarAmp2622K05P070_radius_le :
    (momentScalarAmp2622K05P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P070Expected]

def momentScalarGrow2622K05P070Input : RatPair2542 := (momentPanelGrowth2622K05P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P070Expected : RatState2542 :=
  ((((308450976780679795788116560333349416472025872397638677650734999099495803073328615771740809741277 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1564032048163116904986294912586964952389193160673 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P070_replay :
    compactExp2620 momentScalarGrow2622K05P070Input 20 = momentScalarGrow2622K05P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P070] using h

theorem momentScalarGrow2622K05P070_radius_le :
    (momentScalarGrow2622K05P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P070Expected]

end ConnesWeilRH.Dev
