import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P156 : ℚ := ((-797140808216655721686913508263650907231 : ℚ) / 15084028022235747294289570781410099200)

def momentPanelGrowth2622K05P156 : ℚ := ((13734097520667223752214227228328208696923 : ℚ) / 10266658604067782071630387773749959065600)

theorem momentPanelPhase_owner2622K05P156 :
    (momentPanelPhase2622K05P156 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P156 :
    (momentPanelGrowth2622K05P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P156Input : RatPair2542 := (momentPanelPhase2622K05P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P156Expected : RatState2542 :=
  ((((747182934808077912029858645962147552479540195287194911915190850293021683 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((16364359944488933780257219 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P156_replay :
    compactExp2620 momentScalarAmp2622K05P156Input 20 = momentScalarAmp2622K05P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K05P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P156_replay] at h
  simpa only [momentPanelPhase_owner2622K05P156] using h

theorem momentScalarAmp2622K05P156_radius_le :
    (momentScalarAmp2622K05P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P156Expected]

def momentScalarGrow2622K05P156Input : RatPair2542 := (momentPanelGrowth2622K05P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P156Expected : RatState2542 :=
  ((((4069497360736635870021295505722003542079588803697962848669723272697353727648579966565067116772821 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((10317388381346187889549634656239521801199984472055 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P156_replay :
    compactExp2620 momentScalarGrow2622K05P156Input 20 = momentScalarGrow2622K05P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P156] using h

theorem momentScalarGrow2622K05P156_radius_le :
    (momentScalarGrow2622K05P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P156Expected]

end ConnesWeilRH.Dev
