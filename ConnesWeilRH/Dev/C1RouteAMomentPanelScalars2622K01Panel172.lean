import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P172 : ℚ := ((-683958493959955277147718056895213768429452454208401 : ℚ) / 7293235709727454992207841303886920146915835248640)

def momentPanelGrowth2622K01P172 : ℚ := ((592522139004975526730479227885763795957466697178539211 : ℚ) / 115111344304313652850032594351070060148758339072819200)

theorem momentPanelPhase_owner2622K01P172 :
    (momentPanelPhase2622K01P172 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P172 :
    (momentPanelGrowth2622K01P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P172Input : RatPair2542 := (momentPanelPhase2622K01P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P172Expected : RatState2542 :=
  ((((39951273978442134253893420077469034219657980914199796285 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807314600020513 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P172_replay :
    compactExp2620 momentScalarAmp2622K01P172Input 20 = momentScalarAmp2622K01P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K01P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P172_replay] at h
  simpa only [momentPanelPhase_owner2622K01P172] using h

theorem momentScalarAmp2622K01P172_radius_le :
    (momentScalarAmp2622K01P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P172Expected]

def momentScalarGrow2622K01P172Input : RatPair2542 := (momentPanelGrowth2622K01P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P172Expected : RatState2542 :=
  ((((183674348236716099439858355031402614704019551922881649776384394976523728814433233011564677693698927 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((232833754822172363938420345905808952216843480555207 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P172_replay :
    compactExp2620 momentScalarGrow2622K01P172Input 20 = momentScalarGrow2622K01P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P172] using h

theorem momentScalarGrow2622K01P172_radius_le :
    (momentScalarGrow2622K01P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P172Expected]

end ConnesWeilRH.Dev
