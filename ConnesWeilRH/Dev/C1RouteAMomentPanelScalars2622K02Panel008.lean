import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P008 : ℚ := ((-118438078866277335002548051446452835389171267622627929 : ℚ) / 1277957584048916477499589257045077945117111327129600)

def momentPanelGrowth2622K02P008 : ℚ := ((147597569619550935300180924637385775999904885571114573 : ℚ) / 31911402986904745192617898505130426905840916942028800)

theorem momentPanelPhase_owner2622K02P008 :
    (momentPanelPhase2622K02P008 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P008 :
    (momentPanelGrowth2622K02P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P008Input : RatPair2542 := (momentPanelPhase2622K02P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P008Expected : RatState2542 :=
  ((((60143090576899146901517907782118109036844872596004662141 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((302231454903657312742871 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P008_replay :
    compactExp2620 momentScalarAmp2622K02P008Input 20 = momentScalarAmp2622K02P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K02P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P008_replay] at h
  simpa only [momentPanelPhase_owner2622K02P008] using h

theorem momentScalarAmp2622K02P008_radius_le :
    (momentScalarAmp2622K02P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P008Expected]

def momentScalarGrow2622K02P008Input : RatPair2542 := (momentPanelGrowth2622K02P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P008Expected : RatState2542 :=
  ((((27240832262238159530816803602026263278950316827032134648233407483601591790779887678443330338783613 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((138126820198162258477231197686013557578915624144049 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P008_replay :
    compactExp2620 momentScalarGrow2622K02P008Input 20 = momentScalarGrow2622K02P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P008] using h

theorem momentScalarGrow2622K02P008_radius_le :
    (momentScalarGrow2622K02P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P008Expected]

end ConnesWeilRH.Dev
