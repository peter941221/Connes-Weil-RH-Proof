import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P139 : ℚ := ((-325093859338097413026160754027655683031824505571716021 : ℚ) / 8620290614405456489615835598281060724724513059635200)

def momentPanelGrowth2622K02P139 : ℚ := ((245865314757198472108434193019479024323263592877 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K02P139 :
    (momentPanelPhase2622K02P139 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P139 :
    (momentPanelGrowth2622K02P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P139Input : RatPair2542 := (momentPanelPhase2622K02P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P139Expected : RatState2542 :=
  ((((11171720511348295439651619752725138623071194290351021494312838168777637540060917 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((14162347861764751846180687158569 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P139_replay :
    compactExp2620 momentScalarAmp2622K02P139Input 20 = momentScalarAmp2622K02P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K02P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P139_replay] at h
  simpa only [momentPanelPhase_owner2622K02P139] using h

theorem momentScalarAmp2622K02P139_radius_le :
    (momentScalarAmp2622K02P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P139Expected]

def momentScalarGrow2622K02P139Input : RatPair2542 := (momentPanelGrowth2622K02P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P139Expected : RatState2542 :=
  ((((3792959803442931732700692574478042554839833327648236050809180697874404921854697976782839376210925 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1202036284613574299090233225387018981443562830393 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P139_replay :
    compactExp2620 momentScalarGrow2622K02P139Input 20 = momentScalarGrow2622K02P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P139] using h

theorem momentScalarGrow2622K02P139_radius_le :
    (momentScalarGrow2622K02P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P139Expected]

end ConnesWeilRH.Dev
