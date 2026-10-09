import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P160 : ℚ := ((-218458160607141878316824894702029956871459424047016925 : ℚ) / 3675493930182554476417491893677362259057213354016768)

def momentPanelGrowth2622K03P160 : ℚ := ((1299299290962573499343397943643699497395244645854597475 : ℚ) / 748766292629567833467377300639524906772821309466345472)

theorem momentPanelPhase_owner2622K03P160 :
    (momentPanelPhase2622K03P160 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P160 :
    (momentPanelGrowth2622K03P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P160Input : RatPair2542 := (momentPanelPhase2622K03P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P160Expected : RatState2542 :=
  ((((32862011879640835041202287074791981396835248587786936412508040459823629 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2459511549654601427910309 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P160_replay :
    compactExp2620 momentScalarAmp2622K03P160Input 20 = momentScalarAmp2622K03P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K03P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P160_replay] at h
  simpa only [momentPanelPhase_owner2622K03P160] using h

theorem momentScalarAmp2622K03P160_radius_le :
    (momentScalarAmp2622K03P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P160Expected]

def momentScalarGrow2622K03P160Input : RatPair2542 := (momentPanelGrowth2622K03P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P160Expected : RatState2542 :=
  ((((6055912812194487899499167766060246112525206708357985012334934909824960177627170228161691863700205 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15353537614538019137345815229966106510723004808919 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P160_replay :
    compactExp2620 momentScalarGrow2622K03P160Input 20 = momentScalarGrow2622K03P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P160] using h

theorem momentScalarGrow2622K03P160_radius_le :
    (momentScalarGrow2622K03P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P160Expected]

end ConnesWeilRH.Dev
