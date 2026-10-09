import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P079 : ℚ := ((-100076270585129278859761751158792039425 : ℚ) / 3209407366043425721203717254494027776)

def momentPanelGrowth2622K07P079 : ℚ := ((195784760396604069318440590474900048025 : ℚ) / 1319636322588891376050299861463679893504)

theorem momentPanelPhase_owner2622K07P079 :
    (momentPanelPhase2622K07P079 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P079 :
    (momentPanelGrowth2622K07P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P079Input : RatPair2542 := (momentPanelPhase2622K07P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P079Expected : RatState2542 :=
  ((((61285304101499913618039696664769112058946494002566161351374755199155050444137118261 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19422665708422991929131546464201089 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P079_replay :
    compactExp2620 momentScalarAmp2622K07P079Input 20 = momentScalarAmp2622K07P079Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622K07P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P079]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P079 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P079_replay] at h
  simpa only [momentPanelPhase_owner2622K07P079] using h

theorem momentScalarAmp2622K07P079_radius_le :
    (momentScalarAmp2622K07P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P079Expected]

def momentScalarGrow2622K07P079Input : RatPair2542 := (momentPanelGrowth2622K07P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P079Expected : RatState2542 :=
  ((((2477602889198898385424704828379907359272135659821939511573759290919333779364611382128788497460711 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1570367172619352939158188038201995506139320206957 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P079_replay :
    compactExp2620 momentScalarGrow2622K07P079Input 20 = momentScalarGrow2622K07P079Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P079_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P079] using h

theorem momentScalarGrow2622K07P079_radius_le :
    (momentScalarGrow2622K07P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P079Expected]

end ConnesWeilRH.Dev
