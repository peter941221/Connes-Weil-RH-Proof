import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P063 : ℚ := ((-123060359983447394754557973395297105103773291419558607 : ℚ) / 3538717929295156929095914232653078241147381979545600)

def momentPanelGrowth2622K04P063 : ℚ := ((3473858114550317729485850025039729027800779599732907407 : ℚ) / 12267399585200244106514828406426608369458859987068518400)

theorem momentPanelPhase_owner2622K04P063 :
    (momentPanelPhase2622K04P063 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-53 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P063, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P063 :
    (momentPanelGrowth2622K04P063 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P063, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P063Input : RatPair2542 := (momentPanelPhase2622K04P063 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P063Expected : RatState2542 :=
  ((((842948015392579574253498254699621199198588184741179655002868100012373956823979273 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1068598997753858430191028147627559 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P063_replay :
    compactExp2620 momentScalarAmp2622K04P063Input 20 = momentScalarAmp2622K04P063Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P063_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-53 / 200) 0) -
      (momentScalarAmp2622K04P063Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P063]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P063 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P063 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P063Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P063_replay] at h
  simpa only [momentPanelPhase_owner2622K04P063] using h

theorem momentScalarAmp2622K04P063_radius_le :
    (momentScalarAmp2622K04P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P063Expected]

def momentScalarGrow2622K04P063Input : RatPair2542 := (momentPanelGrowth2622K04P063 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P063Expected : RatState2542 :=
  ((((2835184139283583483439486645569882061356037476636601621937270983163059997507956099256777775882459 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1797010952660035893748491473511635422496348633581 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P063_replay :
    compactExp2620 momentScalarGrow2622K04P063Input 20 = momentScalarGrow2622K04P063Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P063_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P063Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P063]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P063 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P063 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P063Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P063_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P063] using h

theorem momentScalarGrow2622K04P063_radius_le :
    (momentScalarGrow2622K04P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P063Expected]

end ConnesWeilRH.Dev
