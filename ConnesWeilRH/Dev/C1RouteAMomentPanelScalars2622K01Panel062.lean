import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P062 : ℚ := ((-228719941648139748366460647324044558571332806988479 : ℚ) / 7036331125040382213617349829386011022366940856320)

def momentPanelGrowth2622K01P062 : ℚ := ((192352038809678429032877589442148688596536539371 : ℚ) / 963392192576522919714343029378409217058353971200)

theorem momentPanelPhase_owner2622K01P062 :
    (momentPanelPhase2622K01P062 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P062 :
    (momentPanelGrowth2622K01P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P062Input : RatPair2542 := (momentPanelPhase2622K01P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P062Expected : RatState2542 :=
  ((((16315849411238882605409024214118412267230829697600888256960266021418231803006311603 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5170859368188960565337474076503641 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P062_replay :
    compactExp2620 momentScalarAmp2622K01P062Input 20 = momentScalarAmp2622K01P062Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622K01P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P062]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P062 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P062_replay] at h
  simpa only [momentPanelPhase_owner2622K01P062] using h

theorem momentScalarAmp2622K01P062_radius_le :
    (momentScalarAmp2622K01P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P062Expected]

def momentScalarGrow2622K01P062Input : RatPair2542 := (momentPanelGrowth2622K01P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P062Expected : RatState2542 :=
  ((((40750261011373175877928385457349422533825057345835556888504463491419427786970635704102561196377 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((6457135374300925219804867096059672454568577731 : ℚ) / 5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448))

theorem momentScalarGrow2622K01P062_replay :
    compactExp2620 momentScalarGrow2622K01P062Input 20 = momentScalarGrow2622K01P062Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P062_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P062] using h

theorem momentScalarGrow2622K01P062_radius_le :
    (momentScalarGrow2622K01P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P062Expected]

end ConnesWeilRH.Dev
