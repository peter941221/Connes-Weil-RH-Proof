import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P098 : ℚ := ((-28530002649540453740802476228451021591100118573403083 : ℚ) / 944623885417439547278426568880148356014920853094400)

def momentPanelGrowth2622K01P098 : ℚ := ((199215363095292337026848561224509869192345855076807153 : ℚ) / 3510549804513104422532344927217172241373110501743001600)

theorem momentPanelPhase_owner2622K01P098 :
    (momentPanelPhase2622K01P098 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P098 :
    (momentPanelGrowth2622K01P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P098Input : RatPair2542 := (momentPanelPhase2622K01P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P098Expected : RatState2542 :=
  ((((163237388270617364973447128411429316269717142292385064119211709537347194103142391569 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((206933933527675879403318432131103681 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P098_replay :
    compactExp2620 momentScalarAmp2622K01P098Input 20 = momentScalarAmp2622K01P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K01P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P098_replay] at h
  simpa only [momentPanelPhase_owner2622K01P098] using h

theorem momentScalarAmp2622K01P098_radius_le :
    (momentScalarAmp2622K01P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P098Expected]

def momentScalarGrow2622K01P098Input : RatPair2542 := (momentPanelGrowth2622K01P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P098Expected : RatState2542 :=
  ((((1130352234364373673987481121948170395137843858037259925759451259576414001470885011269594627716519 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2865783221630020654085526972057982818040286326987 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P098_replay :
    compactExp2620 momentScalarGrow2622K01P098Input 20 = momentScalarGrow2622K01P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P098] using h

theorem momentScalarGrow2622K01P098_radius_le :
    (momentScalarGrow2622K01P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P098Expected]

end ConnesWeilRH.Dev
