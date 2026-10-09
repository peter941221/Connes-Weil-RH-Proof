import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P101 : ℚ := ((-28524848005678426589962623894392178169424709748311197 : ℚ) / 938914894646615707754193425002350375469389866598400)

def momentPanelGrowth2622K01P101 : ℚ := ((16074141547605980759588461955761267638862691182617 : ℚ) / 211553789251340903369864437821651416590332618342400)

theorem momentPanelPhase_owner2622K01P101 :
    (momentPanelPhase2622K01P101 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (23 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P101 :
    (momentPanelGrowth2622K01P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P101Input : RatPair2542 := (momentPanelPhase2622K01P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P101Expected : RatState2542 :=
  ((((136599300466217678553021675390704232823717588746355557149395524465554565761546743157 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((43291300578749603586467375503772717 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P101_replay :
    compactExp2620 momentScalarAmp2622K01P101Input 20 = momentScalarAmp2622K01P101Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622K01P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P101]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P101 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P101_replay] at h
  simpa only [momentPanelPhase_owner2622K01P101] using h

theorem momentScalarAmp2622K01P101_radius_le :
    (momentScalarAmp2622K01P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P101Expected]

def momentScalarGrow2622K01P101Input : RatPair2542 := (momentPanelGrowth2622K01P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P101Expected : RatState2542 :=
  ((((2304607078891953871694824140304292598070455979611285108098976561156479725119408883417324851891679 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((730359083789017175320064259017880952753276411679 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P101_replay :
    compactExp2620 momentScalarGrow2622K01P101Input 20 = momentScalarGrow2622K01P101Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P101_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P101] using h

theorem momentScalarGrow2622K01P101_radius_le :
    (momentScalarGrow2622K01P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P101Expected]

end ConnesWeilRH.Dev
