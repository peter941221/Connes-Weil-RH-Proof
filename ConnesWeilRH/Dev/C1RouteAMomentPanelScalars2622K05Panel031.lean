import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P031 : ℚ := ((-2477944774468884293738128261895191543443 : ℚ) / 53365047908167910052447612858636697600)

def momentPanelGrowth2622K05P031 : ℚ := ((12169352043406980048825560457026021722043 : ℚ) / 14365814714604199270991823047658936729600)

theorem momentPanelPhase_owner2622K05P031 :
    (momentPanelPhase2622K05P031 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P031 :
    (momentPanelGrowth2622K05P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P031Input : RatPair2542 := (momentPanelPhase2622K05P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P031Expected : RatState2542 :=
  ((((1821975864822072824740168385478078231993329462572099692066371569383543339057 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9240133236519172684490492811 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P031_replay :
    compactExp2620 momentScalarAmp2622K05P031Input 20 = momentScalarAmp2622K05P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K05P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P031_replay] at h
  simpa only [momentPanelPhase_owner2622K05P031] using h

theorem momentScalarAmp2622K05P031_radius_le :
    (momentScalarAmp2622K05P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P031Expected]

def momentScalarGrow2622K05P031Input : RatPair2542 := (momentPanelGrowth2622K05P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P031Expected : RatState2542 :=
  ((((2491504068335283831188265496639938528995863389668176193174329181127376706814078647208368331374565 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((197397129761277290700850272078513139998976496413 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P031_replay :
    compactExp2620 momentScalarGrow2622K05P031Input 20 = momentScalarGrow2622K05P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P031] using h

theorem momentScalarGrow2622K05P031_radius_le :
    (momentScalarGrow2622K05P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P031Expected]

end ConnesWeilRH.Dev
