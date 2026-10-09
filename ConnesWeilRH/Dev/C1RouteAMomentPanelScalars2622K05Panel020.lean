import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P020 : ℚ := ((-825008396628380774985972502813666180303 : ℚ) / 13980664939797096423226840311450828800)

def momentPanelGrowth2622K05P020 : ℚ := ((1432176541799180780408358231888444163 : ℚ) / 879242456318299912878113343248793600)

theorem momentPanelPhase_owner2622K05P020 :
    (momentPanelPhase2622K05P020 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-139 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P020 :
    (momentPanelGrowth2622K05P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P020Input : RatPair2542 := (momentPanelPhase2622K05P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P020Expected : RatState2542 :=
  ((((25151305180824769801633889082882097101558710045847021694298683316247923 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((620405340528285587397127 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P020_replay :
    compactExp2620 momentScalarAmp2622K05P020Input 20 = momentScalarAmp2622K05P020Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622K05P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P020]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P020 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P020_replay] at h
  simpa only [momentPanelPhase_owner2622K05P020] using h

theorem momentScalarAmp2622K05P020_radius_le :
    (momentScalarAmp2622K05P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P020Expected]

def momentScalarGrow2622K05P020Input : RatPair2542 := (momentPanelGrowth2622K05P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P020Expected : RatState2542 :=
  ((((10889558607723333378732317468072736504710386679147452444356501367368369800915400437822518909881499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1725516757713854893790782633115253916373582406631 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K05P020_replay :
    compactExp2620 momentScalarGrow2622K05P020Input 20 = momentScalarGrow2622K05P020Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P020_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P020] using h

theorem momentScalarGrow2622K05P020_radius_le :
    (momentScalarGrow2622K05P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P020Expected]

end ConnesWeilRH.Dev
