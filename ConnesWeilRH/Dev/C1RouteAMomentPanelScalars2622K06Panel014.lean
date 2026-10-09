import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P014 : ℚ := ((-20865683 : ℚ) / 286650)

def momentPanelGrowth2622K06P014 : ℚ := ((1507607 : ℚ) / 580800)

theorem momentPanelPhase_owner2622K06P014 :
    (momentPanelPhase2622K06P014 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P014 :
    (momentPanelGrowth2622K06P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P014Input : RatPair2542 := (momentPanelPhase2622K06P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P014Expected : RatState2542 :=
  ((((52077790799216632765688131098750170831899662709145593686237041929 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462926312571212356727 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P014_replay :
    compactExp2620 momentScalarAmp2622K06P014Input 20 = momentScalarAmp2622K06P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K06P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P014_replay] at h
  simpa only [momentPanelPhase_owner2622K06P014] using h

theorem momentScalarAmp2622K06P014_radius_le :
    (momentScalarAmp2622K06P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P014Expected]

def momentScalarGrow2622K06P014Input : RatPair2542 := (momentPanelGrowth2622K06P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P014Expected : RatState2542 :=
  ((((28636179379615268770458792729449557371516678497526400867911705380047527245557291805934302353329997 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4537572514610693105548411372948628525845153406135 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P014_replay :
    compactExp2620 momentScalarGrow2622K06P014Input 20 = momentScalarGrow2622K06P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P014] using h

theorem momentScalarGrow2622K06P014_radius_le :
    (momentScalarGrow2622K06P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P014Expected]

end ConnesWeilRH.Dev
