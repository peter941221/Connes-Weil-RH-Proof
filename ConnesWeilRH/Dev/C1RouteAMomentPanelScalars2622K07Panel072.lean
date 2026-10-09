import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P072 : ℚ := ((-1357336085935216544485663279357451125 : ℚ) / 41944023060351654436722915659481088)

def momentPanelGrowth2622K07P072 : ℚ := ((46545356578907817247470397246251333075 : ℚ) / 237367514045507144475246403364902141952)

theorem momentPanelPhase_owner2622K07P072 :
    (momentPanelPhase2622K07P072 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-7 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P072, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P072 :
    (momentPanelGrowth2622K07P072 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P072, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P072Input : RatPair2542 := (momentPanelPhase2622K07P072 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P072Expected : RatState2542 :=
  ((((1178757474280353556402774305910065354594734787275315427279523705642320625887679821 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((23908779769183864737020098521275443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P072_replay :
    compactExp2620 momentScalarAmp2622K07P072Input 20 = momentScalarAmp2622K07P072Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P072_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-7 / 40) 0) -
      (momentScalarAmp2622K07P072Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P072]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P072 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P072 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P072Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P072_replay] at h
  simpa only [momentPanelPhase_owner2622K07P072] using h

theorem momentScalarAmp2622K07P072_radius_le :
    (momentScalarAmp2622K07P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P072Expected]

def momentScalarGrow2622K07P072Input : RatPair2542 := (momentPanelGrowth2622K07P072 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P072Expected : RatState2542 :=
  ((((1299359571582424915999145454798945330141831668729020868180360806812429504224397252146292702394095 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3294267265610240441255469167293511499670412844001 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P072_replay :
    compactExp2620 momentScalarGrow2622K07P072Input 20 = momentScalarGrow2622K07P072Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P072_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P072Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P072]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P072 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P072 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P072Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P072_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P072] using h

theorem momentScalarGrow2622K07P072_radius_le :
    (momentScalarGrow2622K07P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P072Expected]

end ConnesWeilRH.Dev
