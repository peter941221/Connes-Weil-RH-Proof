import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P120 : ℚ := ((-72875609899335962024727232227919756594457767723664975 : ℚ) / 2209242412530326123729645085254751319587399030276096)

def momentPanelGrowth2622K03P120 : ℚ := ((573696286697150307778706834247748275677641098442081475 : ℚ) / 2487704785774996052633667625150339932050039527075479552)

theorem momentPanelPhase_owner2622K03P120 :
    (momentPanelPhase2622K03P120 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (61 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P120 :
    (momentPanelGrowth2622K03P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P120Input : RatPair2542 := (momentPanelPhase2622K03P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P120Expected : RatState2542 :=
  ((((10084588023515972538628700200620296920785411387241189281809422789124053916775888161 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12784136227745119152198486913088697 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P120_replay :
    compactExp2620 momentScalarAmp2622K03P120Input 20 = momentScalarAmp2622K03P120Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622K03P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P120]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P120 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P120_replay] at h
  simpa only [momentPanelPhase_owner2622K03P120] using h

theorem momentScalarAmp2622K03P120_radius_le :
    (momentScalarAmp2622K03P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P120Expected]

def momentScalarGrow2622K03P120Input : RatPair2542 := (momentPanelGrowth2622K03P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P120Expected : RatState2542 :=
  ((((1345000465071800185131025258253746625107289658265212910589492552464834747114928085240473735378807 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3409980543755982412752318856708009830044680800779 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P120_replay :
    compactExp2620 momentScalarGrow2622K03P120Input 20 = momentScalarGrow2622K03P120Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P120_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P120] using h

theorem momentScalarGrow2622K03P120_radius_le :
    (momentScalarGrow2622K03P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P120Expected]

end ConnesWeilRH.Dev
