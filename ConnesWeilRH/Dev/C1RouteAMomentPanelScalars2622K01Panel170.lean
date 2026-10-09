import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P170 : ℚ := ((-28494752651175687007343959862271817338704484280660571 : ℚ) / 334903671093453486090326802731324033752211495321600)

def momentPanelGrowth2622K01P170 : ℚ := ((1734891728582142761085155562701877725644074717896530833 : ℚ) / 421991506488178063761738322472342564221392338393497600)

theorem momentPanelPhase_owner2622K01P170 :
    (momentPanelPhase2622K01P170 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P170 :
    (momentPanelGrowth2622K01P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P170Input : RatPair2542 := (momentPanelPhase2622K01P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P170Expected : RatState2542 :=
  ((((119482690009918463929549610038582832898360807697832810292089 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229561300218077 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P170_replay :
    compactExp2620 momentScalarAmp2622K01P170Input 20 = momentScalarAmp2622K01P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K01P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P170_replay] at h
  simpa only [momentPanelPhase_owner2622K01P170] using h

theorem momentScalarAmp2622K01P170_radius_le :
    (momentScalarAmp2622K01P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P170Expected]

def momentScalarGrow2622K01P170Input : RatPair2542 := (momentPanelGrowth2622K01P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P170Expected : RatState2542 :=
  ((((130337786379699369789850829434188735320886689329521720578090040151656650181277907326415655057010271 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((82611062670660134289745394455430012689382718515593 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P170_replay :
    compactExp2620 momentScalarGrow2622K01P170Input 20 = momentScalarGrow2622K01P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P170] using h

theorem momentScalarGrow2622K01P170_radius_le :
    (momentScalarGrow2622K01P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P170Expected]

end ConnesWeilRH.Dev
