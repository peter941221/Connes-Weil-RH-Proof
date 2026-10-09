import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P112 : ℚ := ((-8750526151248874671826116628301822806768041699565125 : ℚ) / 277502623388205191593924657612004238357170191597568)

def momentPanelGrowth2622K03P112 : ℚ := ((428266876685936846336639483261262624423750630428013475 : ℚ) / 2731176343537951169777219481432545520294521329409851392)

theorem momentPanelPhase_owner2622K03P112 :
    (momentPanelPhase2622K03P112 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P112 :
    (momentPanelGrowth2622K03P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P112Input : RatPair2542 := (momentPanelPhase2622K03P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P112Expected : RatState2542 :=
  ((((43145398741177546342555170633659107748071544020038930035771761290823959453910693745 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1709216731046381195117146486578575 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K03P112_replay :
    compactExp2620 momentScalarAmp2622K03P112Input 20 = momentScalarAmp2622K03P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K03P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P112_replay] at h
  simpa only [momentPanelPhase_owner2622K03P112] using h

theorem momentScalarAmp2622K03P112_radius_le :
    (momentScalarAmp2622K03P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P112Expected]

def momentScalarGrow2622K03P112Input : RatPair2542 := (momentPanelGrowth2622K03P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P112Expected : RatState2542 :=
  ((((1249306275610764162187082165495331508266134929296817082381995348419148805387435185778909004770287 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3167367226637497456842616162245747680717378143265 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P112_replay :
    compactExp2620 momentScalarGrow2622K03P112Input 20 = momentScalarGrow2622K03P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P112] using h

theorem momentScalarGrow2622K03P112_radius_le :
    (momentScalarGrow2622K03P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P112Expected]

end ConnesWeilRH.Dev
