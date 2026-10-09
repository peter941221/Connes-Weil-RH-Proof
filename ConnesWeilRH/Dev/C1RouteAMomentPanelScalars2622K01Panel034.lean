import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P034 : ℚ := ((-85838993551836241202012358545150661298500026443360737 : ℚ) / 1975239444320413177390614867419628793996902190284800)

def momentPanelGrowth2622K01P034 : ℚ := ((1565128134315588357379754424860279834942504570399731 : ℚ) / 2188934105110813020582066734195454453291808928563200)

theorem momentPanelPhase_owner2622K01P034 :
    (momentPanelPhase2622K01P034 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-111 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P034, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P034 :
    (momentPanelGrowth2622K01P034 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P034, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P034Input : RatPair2542 := (momentPanelPhase2622K01P034 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P034Expected : RatState2542 :=
  ((((285917396388528825690785868127800134596043123258229264005208073362498114486563 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((181230399263432328473444157017 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P034_replay :
    compactExp2620 momentScalarAmp2622K01P034Input 20 = momentScalarAmp2622K01P034Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P034_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-111 / 200) 0) -
      (momentScalarAmp2622K01P034Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P034]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P034 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P034 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P034Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P034_replay] at h
  simpa only [momentPanelPhase_owner2622K01P034] using h

theorem momentScalarAmp2622K01P034_radius_le :
    (momentScalarAmp2622K01P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P034Expected]

def momentScalarGrow2622K01P034Input : RatPair2542 := (momentPanelGrowth2622K01P034 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P034Expected : RatState2542 :=
  ((((4366436539690471801414175119745506931773847814006372021087226241360699404333605891754263386387599 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1383778031508086326120354329734111753860216407965 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P034_replay :
    compactExp2620 momentScalarGrow2622K01P034Input 20 = momentScalarGrow2622K01P034Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P034_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P034Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P034]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P034 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P034 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P034Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P034_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P034] using h

theorem momentScalarGrow2622K01P034_radius_le :
    (momentScalarGrow2622K01P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P034Expected]

end ConnesWeilRH.Dev
