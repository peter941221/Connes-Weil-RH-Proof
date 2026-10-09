import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P000 : ℚ := ((-28576505932690341540900773336609221332346354081936151 : ℚ) / 189324406437445578222381633847475529841171339673600)

def momentPanelGrowth2622K01P000 : ℚ := ((192702423800991879983872791029393303224833932414553 : ℚ) / 12880910426671287926551030874281693605854288281600)

theorem momentPanelPhase_owner2622K01P000 :
    (momentPanelPhase2622K01P000 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-179 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P000, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P000 :
    (momentPanelGrowth2622K01P000 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P000, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P000Input : RatPair2542 := (momentPanelPhase2622K01P000 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P000Expected : RatState2542 :=
  ((((5990522816651196529667827089641 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P000_replay :
    compactExp2620 momentScalarAmp2622K01P000Input 20 = momentScalarAmp2622K01P000Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P000_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-179 / 200) 0) -
      (momentScalarAmp2622K01P000Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P000]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P000 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P000 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P000Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P000_replay] at h
  simpa only [momentPanelPhase_owner2622K01P000] using h

theorem momentScalarAmp2622K01P000_radius_le :
    (momentScalarAmp2622K01P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P000Expected]

def momentScalarGrow2622K01P000Input : RatPair2542 := (momentPanelGrowth2622K01P000 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P000Expected : RatState2542 :=
  ((((838859192452479026238091335369566717551917740924544643521722126506868470981238922783635813766093972263 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4253460749596193161398051779587821652842705379878478759 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P000_replay :
    compactExp2620 momentScalarGrow2622K01P000Input 20 = momentScalarGrow2622K01P000Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P000_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P000Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P000]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P000 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P000 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P000Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P000_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P000] using h

theorem momentScalarGrow2622K01P000_radius_le :
    (momentScalarGrow2622K01P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P000Expected]

end ConnesWeilRH.Dev
