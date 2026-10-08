import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P067 : ℚ := ((-2925092356794219807436274169790727050839126158722617 : ℚ) / 86719569808814122373101455503751324486615684874240)

def momentPanelGrowth2622K04P067 : ℚ := ((1060660639845365278399109045122788119895052386387838069 : ℚ) / 4267463036778048702776905439738352375460189577202892800)

theorem momentPanelPhase_owner2622K04P067 :
    (momentPanelPhase2622K04P067 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P067 :
    (momentPanelGrowth2622K04P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P067Input : RatPair2542 := (momentPanelPhase2622K04P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P067Expected : RatState2542 :=
  ((((2396674609661959288371366555120167144371023621649888768285823031684880506979241181 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6076487482025287814216594980211705 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P067_replay :
    compactExp2620 momentScalarAmp2622K04P067Input 20 = momentScalarAmp2622K04P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K04P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P067_replay] at h
  simpa only [momentPanelPhase_owner2622K04P067] using h

theorem momentScalarAmp2622K04P067_radius_le :
    (momentScalarAmp2622K04P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P067Expected]

def momentScalarGrow2622K04P067Input : RatPair2542 := (momentPanelGrowth2622K04P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P067Expected : RatState2542 :=
  ((((1369338282587401657532777983077104187075700714825669785411996238368767843955299589687199797788675 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((867921042193720649027025187353459480912241912495 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P067_replay :
    compactExp2620 momentScalarGrow2622K04P067Input 20 = momentScalarGrow2622K04P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P067] using h

theorem momentScalarGrow2622K04P067_radius_le :
    (momentScalarGrow2622K04P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P067Expected]

end ConnesWeilRH.Dev
