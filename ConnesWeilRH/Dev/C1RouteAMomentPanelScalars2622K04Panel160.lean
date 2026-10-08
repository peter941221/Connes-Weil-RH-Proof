import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P160 : ℚ := ((-304197634496212073341467891831279628968684643518355467 : ℚ) / 5742959265910241369402331083870878529776895865651200)

def momentPanelGrowth2622K04P160 : ℚ := ((2137485174430274972104163807934601207011771606906344629 : ℚ) / 1169947332233699739792777032249257666832533296041164800)

theorem momentPanelPhase_owner2622K04P160 :
    (momentPanelPhase2622K04P160 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P160 :
    (momentPanelGrowth2622K04P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P160Input : RatPair2542 := (momentPanelPhase2622K04P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P160Expected : RatState2542 :=
  ((((21161334191871596104851424478014748803200587869476245502805295531044975723 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7311096184187611647314339 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P160_replay :
    compactExp2620 momentScalarAmp2622K04P160Input 20 = momentScalarAmp2622K04P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K04P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P160_replay] at h
  simpa only [momentPanelPhase_owner2622K04P160] using h

theorem momentScalarAmp2622K04P160_radius_le :
    (momentScalarAmp2622K04P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P160Expected]

def momentScalarGrow2622K04P160Input : RatPair2542 := (momentPanelGrowth2622K04P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P160Expected : RatState2542 :=
  ((((13275516839448096062599220315497812689036570533476033608036470307242864614924518077357852138969413 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8414343784138320693829421377456612120892267926619 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P160_replay :
    compactExp2620 momentScalarGrow2622K04P160Input 20 = momentScalarGrow2622K04P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P160] using h

theorem momentScalarGrow2622K04P160_radius_le :
    (momentScalarGrow2622K04P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P160Expected]

end ConnesWeilRH.Dev
