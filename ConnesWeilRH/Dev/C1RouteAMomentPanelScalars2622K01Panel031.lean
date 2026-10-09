import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P031 : ℚ := ((-85839393395186008923826106983530261201978186458691651 : ℚ) / 1877615702139325521526228107109283326668322321203200)

def momentPanelGrowth2622K01P031 : ℚ := ((421979261725489146415819161530644830253211671343951851 : ℚ) / 505452170277852032640425340707751383988348478763827200)

theorem momentPanelPhase_owner2622K01P031 :
    (momentPanelPhase2622K01P031 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P031 :
    (momentPanelGrowth2622K01P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P031Input : RatPair2542 := (momentPanelPhase2622K01P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P031Expected : RatState2542 :=
  ((((14921994020613325514790015143599468349759563889023322982149609000524224509329 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((37835816680956994430326958409 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P031_replay :
    compactExp2620 momentScalarAmp2622K01P031Input 20 = momentScalarAmp2622K01P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K01P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P031_replay] at h
  simpa only [momentPanelPhase_owner2622K01P031] using h

theorem momentScalarAmp2622K01P031_radius_le :
    (momentScalarAmp2622K01P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P031Expected]

def momentScalarGrow2622K01P031Input : RatPair2542 := (momentPanelGrowth2622K01P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P031Expected : RatState2542 :=
  ((((4922339040094653120875399515492697525235042621941241539919515922516812040029541066264900725911749 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1559950267674395561352355014733459928306648539269 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P031_replay :
    compactExp2620 momentScalarGrow2622K01P031Input 20 = momentScalarGrow2622K01P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P031] using h

theorem momentScalarGrow2622K01P031_radius_le :
    (momentScalarGrow2622K01P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P031Expected]

end ConnesWeilRH.Dev
