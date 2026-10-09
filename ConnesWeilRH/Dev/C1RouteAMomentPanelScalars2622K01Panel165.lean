import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P165 : ℚ := ((-28487436806834888760598888318573288695969323215840541 : ℚ) / 409120551114163399905357673142697780844114319769600)

def momentPanelGrowth2622K01P165 : ℚ := ((33126786822225371462239295691287231311764386807099 : ℚ) / 12952272811306585920603945172754168362673425612800)

theorem momentPanelPhase_owner2622K01P165 :
    (momentPanelPhase2622K01P165 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (151 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P165, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P165 :
    (momentPanelGrowth2622K01P165 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P165, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P165Input : RatPair2542 := (momentPanelPhase2622K01P165 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P165Expected : RatState2542 :=
  ((((1228225369636240883360694772018573512988222788726544185621020519049 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604463299073320696060875 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P165_replay :
    compactExp2620 momentScalarAmp2622K01P165Input 20 = momentScalarAmp2622K01P165Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P165_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (151 / 200) 0) -
      (momentScalarAmp2622K01P165Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P165]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P165 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P165 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P165Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P165_replay] at h
  simpa only [momentPanelPhase_owner2622K01P165] using h

theorem momentScalarAmp2622K01P165_radius_le :
    (momentScalarAmp2622K01P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P165Expected]

def momentScalarGrow2622K01P165Input : RatPair2542 := (momentPanelGrowth2622K01P165 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P165Expected : RatState2542 :=
  ((((13782309246038394285568820996125836450633509703139190027839501850145617710450005958669909834254555 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((17471109974061477178953565875597855491023414128675 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P165_replay :
    compactExp2620 momentScalarGrow2622K01P165Input 20 = momentScalarGrow2622K01P165Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P165_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P165Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P165]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P165 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P165 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P165Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P165_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P165] using h

theorem momentScalarGrow2622K01P165_radius_le :
    (momentScalarGrow2622K01P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P165Expected]

end ConnesWeilRH.Dev
