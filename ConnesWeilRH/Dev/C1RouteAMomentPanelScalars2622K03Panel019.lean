import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P019 : ℚ := ((-219992330592128997144280555112854949025320338845783075 : ℚ) / 3675493930182554476417491893677362259057213354016768)

def momentPanelGrowth2622K03P019 : ℚ := ((1299299290962573499343397943643699497395244645854597475 : ℚ) / 748766292629567833467377300639524906772821309466345472)

theorem momentPanelPhase_owner2622K03P019 :
    (momentPanelPhase2622K03P019 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P019 :
    (momentPanelGrowth2622K03P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P019Input : RatPair2542 := (momentPanelPhase2622K03P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P019Expected : RatState2542 :=
  ((((21647981493175774296511513215844364333941182832858834416860163167702127 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((305661910303803911179161 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P019_replay :
    compactExp2620 momentScalarAmp2622K03P019Input 20 = momentScalarAmp2622K03P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K03P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P019_replay] at h
  simpa only [momentPanelPhase_owner2622K03P019] using h

theorem momentScalarAmp2622K03P019_radius_le :
    (momentScalarAmp2622K03P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P019Expected]

def momentScalarGrow2622K03P019Input : RatPair2542 := (momentPanelGrowth2622K03P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P019Expected : RatState2542 :=
  ((((6055912812194487899499167766060246112525206708357985012334934909824960177627170228161691863700205 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15353537614538019137345815229966106510723004808919 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P019_replay :
    compactExp2620 momentScalarGrow2622K03P019Input 20 = momentScalarGrow2622K03P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P019] using h

theorem momentScalarGrow2622K03P019_radius_le :
    (momentScalarGrow2622K03P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P019Expected]

end ConnesWeilRH.Dev
