import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P176 : ℚ := ((-28506367376276982285792778740639151723354552176976247 : ℚ) / 239563525220695366035633299972097758641844020838400)

def momentPanelGrowth2622K01P176 : ℚ := ((1862950890798254487824223672841239325990284346041840753 : ℚ) / 210867318792341654316072428727495445667110926784921600)

theorem momentPanelPhase_owner2622K01P176 :
    (momentPanelPhase2622K01P176 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (173 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P176, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P176 :
    (momentPanelGrowth2622K01P176 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P176, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P176Input : RatPair2542 := (momentPanelPhase2622K01P176 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P176Expected : RatState2542 :=
  ((((14011120519965431072239816398710384106496603 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P176_replay :
    compactExp2620 momentScalarAmp2622K01P176Input 20 = momentScalarAmp2622K01P176Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P176_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (173 / 200) 0) -
      (momentScalarAmp2622K01P176Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P176]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P176 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P176 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P176Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P176_replay] at h
  simpa only [momentPanelPhase_owner2622K01P176] using h

theorem momentScalarAmp2622K01P176_radius_le :
    (momentScalarAmp2622K01P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P176Expected]

def momentScalarGrow2622K01P176Input : RatPair2542 := (momentPanelGrowth2622K01P176 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P176Expected : RatState2542 :=
  ((((7335554326131255568615483436873513907980418102783220113014015383972936064585843168000604089470521777 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4649420748716584118208264126790814782631557507660667 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P176_replay :
    compactExp2620 momentScalarGrow2622K01P176Input 20 = momentScalarGrow2622K01P176Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P176_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P176Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P176]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P176 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P176 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P176Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P176_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P176] using h

theorem momentScalarGrow2622K01P176_radius_le :
    (momentScalarGrow2622K01P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P176Expected]

end ConnesWeilRH.Dev
