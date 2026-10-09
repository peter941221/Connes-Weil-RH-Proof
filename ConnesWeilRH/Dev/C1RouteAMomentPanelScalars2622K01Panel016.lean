import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P016 : ℚ := ((-85814483911925554190494032036222883366651338444781221 : ℚ) / 1312425615827765408627146863207283252660754658099200)

def momentPanelGrowth2622K01P016 : ℚ := ((33033432572518810052895720370764916345624397942695651 : ℚ) / 15213996548745402895119984491391547067920754619187200)

theorem momentPanelPhase_owner2622K01P016 :
    (momentPanelPhase2622K01P016 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-147 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P016 :
    (momentPanelGrowth2622K01P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P016Input : RatPair2542 := (momentPanelPhase2622K01P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P016Expected : RatState2542 :=
  ((((42826833407014562845215798361028147933410172354868221961967083247101 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((151122514057644780352529 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K01P016_replay :
    compactExp2620 momentScalarAmp2622K01P016Input 20 = momentScalarAmp2622K01P016Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622K01P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P016]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P016 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P016_replay] at h
  simpa only [momentPanelPhase_owner2622K01P016] using h

theorem momentScalarAmp2622K01P016_radius_le :
    (momentScalarAmp2622K01P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P016Expected]

def momentScalarGrow2622K01P016Input : RatPair2542 := (momentPanelGrowth2622K01P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P016Expected : RatState2542 :=
  ((((18731032671808081037463890479865800280613516612620274827328890899077852001686024226568493520609785 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5936088910645779558909887603629122100898866121389 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P016_replay :
    compactExp2620 momentScalarGrow2622K01P016Input 20 = momentScalarGrow2622K01P016Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P016_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P016] using h

theorem momentScalarGrow2622K01P016_radius_le :
    (momentScalarGrow2622K01P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P016Expected]

end ConnesWeilRH.Dev
