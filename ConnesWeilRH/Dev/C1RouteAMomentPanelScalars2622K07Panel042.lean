import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P042 : ℚ := ((-1426570457823247145958072708795876625 : ℚ) / 33506540665232559540360859124498432)

def momentPanelGrowth2622K07P042 : ℚ := ((5321258977963851388777824917040618075 : ℚ) / 9385117136620908241909720009567895552)

theorem momentPanelPhase_owner2622K07P042 :
    (momentPanelPhase2622K07P042 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P042 :
    (momentPanelGrowth2622K07P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P042Input : RatPair2542 := (momentPanelPhase2622K07P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P042Expected : RatState2542 :=
  ((((690444579191595142261907638848409336495086087395231947247426500829883946694171 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((218820110434592636853994368411 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P042_replay :
    compactExp2620 momentScalarAmp2622K07P042Input 20 = momentScalarAmp2622K07P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K07P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P042_replay] at h
  simpa only [momentPanelPhase_owner2622K07P042] using h

theorem momentScalarAmp2622K07P042_radius_le :
    (momentScalarAmp2622K07P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P042Expected]

def momentScalarGrow2622K07P042Input : RatPair2542 := (momentPanelGrowth2622K07P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P042Expected : RatState2542 :=
  ((((3765640388743071571992014401326896768466061926032843558028240866714722768566329268296013679569051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((596689214735600673569342560402847605055897006625 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P042_replay :
    compactExp2620 momentScalarGrow2622K07P042Input 20 = momentScalarGrow2622K07P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P042] using h

theorem momentScalarGrow2622K07P042_radius_le :
    (momentScalarGrow2622K07P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P042Expected]

end ConnesWeilRH.Dev
