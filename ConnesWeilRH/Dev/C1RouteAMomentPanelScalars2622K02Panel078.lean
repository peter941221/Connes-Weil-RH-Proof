import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P078 : ℚ := ((-115945619589143347402161792057174470708933071560819869 : ℚ) / 3755659578586462831016773700009401501877559466393600)

def momentPanelGrowth2622K02P078 : ℚ := ((97317912533150030773493850426464206413736948258791 : ℚ) / 846215157005363613479457751286605666361330473369600)

theorem momentPanelPhase_owner2622K02P078 :
    (momentPanelPhase2622K02P078 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P078 :
    (momentPanelGrowth2622K02P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P078Input : RatPair2542 := (momentPanelPhase2622K02P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P078Expected : RatState2542 :=
  ((((83551765517399502192958283585388768733950574012891687925433420417561406543070878325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26479391024046353179377307429821151 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P078_replay :
    compactExp2620 momentScalarAmp2622K02P078Input 20 = momentScalarAmp2622K02P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K02P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P078_replay] at h
  simpa only [momentPanelPhase_owner2622K02P078] using h

theorem momentScalarAmp2622K02P078_radius_le :
    (momentScalarAmp2622K02P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P078Expected]

def momentScalarGrow2622K02P078Input : RatPair2542 := (momentPanelGrowth2622K02P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P078Expected : RatState2542 :=
  ((((1198158046961192454372536303614375732454772378392584206294274917179079517078686834337564087735991 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3037691201635079417084620844182709614246536374199 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P078_replay :
    compactExp2620 momentScalarGrow2622K02P078Input 20 = momentScalarGrow2622K02P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P078] using h

theorem momentScalarGrow2622K02P078_radius_le :
    (momentScalarGrow2622K02P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P078Expected]

end ConnesWeilRH.Dev
