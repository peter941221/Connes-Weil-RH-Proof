import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P004 : ℚ := ((-353275034489864566128631690624382679893658015658669731 : ℚ) / 3071151585164684472061219749061423634468394185523200)

def momentPanelGrowth2622K02P004 : ℚ := ((154253452116199454892615218948449810701163076480579293 : ℚ) / 20162299980549283451746088404622182943138146733260800)

theorem momentPanelPhase_owner2622K02P004 :
    (momentPanelPhase2622K02P004 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P004 :
    (momentPanelGrowth2622K02P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P004Input : RatPair2542 := (momentPanelPhase2622K02P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P004Expected : RatState2542 :=
  ((((11792563754826121065169410665238955721134472407 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P004_replay :
    compactExp2620 momentScalarAmp2622K02P004Input 20 = momentScalarAmp2622K02P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K02P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P004_replay] at h
  simpa only [momentPanelPhase_owner2622K02P004] using h

theorem momentScalarAmp2622K02P004_radius_le :
    (momentScalarAmp2622K02P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P004Expected]

def momentScalarGrow2622K02P004Input : RatPair2542 := (momentPanelGrowth2622K02P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P004Expected : RatState2542 :=
  ((((4489591257584717461862772146555304178977134605863723314008687437930389147103658315582208318631594085 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5691191528407900196103385879669108350731413656818157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P004_replay :
    compactExp2620 momentScalarGrow2622K02P004Input 20 = momentScalarGrow2622K02P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P004] using h

theorem momentScalarGrow2622K02P004_radius_le :
    (momentScalarGrow2622K02P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P004Expected]

end ConnesWeilRH.Dev
