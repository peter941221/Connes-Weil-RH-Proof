import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P116 : ℚ := ((-105299270849506186214767781716622116717466168420441393 : ℚ) / 3538717929295156929095914232653078241147381979545600)

def momentPanelGrowth2622K04P116 : ℚ := ((3473858114550317729485850025039729027800779599732907407 : ℚ) / 12267399585200244106514828406426608369458859987068518400)

theorem momentPanelPhase_owner2622K04P116 :
    (momentPanelPhase2622K04P116 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P116 :
    (momentPanelGrowth2622K04P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P116Input : RatPair2542 := (momentPanelPhase2622K04P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P116Expected : RatState2542 :=
  ((((255027594104202478130631869082663597810313324246172796295022259654435120955170982345 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((80823764258039111062672346793610927 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P116_replay :
    compactExp2620 momentScalarAmp2622K04P116Input 20 = momentScalarAmp2622K04P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K04P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P116_replay] at h
  simpa only [momentPanelPhase_owner2622K04P116] using h

theorem momentScalarAmp2622K04P116_radius_le :
    (momentScalarAmp2622K04P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P116Expected]

def momentScalarGrow2622K04P116Input : RatPair2542 := (momentPanelGrowth2622K04P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P116Expected : RatState2542 :=
  ((((2835184139283583483439486645569882061356037476636601621937270983163059997507956099256777775882459 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1797010952660035893748491473511635422496348633581 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P116_replay :
    compactExp2620 momentScalarGrow2622K04P116Input 20 = momentScalarGrow2622K04P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P116] using h

theorem momentScalarGrow2622K04P116_radius_le :
    (momentScalarGrow2622K04P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P116Expected]

end ConnesWeilRH.Dev
