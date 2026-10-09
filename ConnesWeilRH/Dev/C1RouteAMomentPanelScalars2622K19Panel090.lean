import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P090 : ℚ := ((-811086966741671911211202629035478535123 : ℚ) / 27042536724548772176248870139645132800)

def momentPanelGrowth2622K19P090 : ℚ := ((726275989854364174144076096836400995123 : ℚ) / 33797255540925060210631943458718849433600)

theorem momentPanelPhase_owner2622K19P090 :
    (momentPanelPhase2622K19P090 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (1 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P090, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P090 :
    (momentPanelGrowth2622K19P090 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P090, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P090Input : RatPair2542 := (momentPanelPhase2622K19P090 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P090Expected : RatState2542 :=
  ((((100640226883298600136641343696989233579470786514288511133502815411302163315637425743 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((127580293215246802126174743399601397 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K19P090_replay :
    compactExp2620 momentScalarAmp2622K19P090Input 20 = momentScalarAmp2622K19P090Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P090_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (1 / 200) 0) -
      (momentScalarAmp2622K19P090Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P090]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P090 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P090 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P090Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P090_replay] at h
  simpa only [momentPanelPhase_owner2622K19P090] using h

theorem momentScalarAmp2622K19P090_radius_le :
    (momentScalarAmp2622K19P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P090Expected]

def momentScalarGrow2622K19P090Input : RatPair2542 := (momentPanelGrowth2622K19P090 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P090Expected : RatState2542 :=
  ((((2182384424849765573735079784520059937920133842716621115805365329797698721330331509317565160954229 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2766500869393709860016463750930310007615479598553 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K19P090_replay :
    compactExp2620 momentScalarGrow2622K19P090Input 20 = momentScalarGrow2622K19P090Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P090_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P090Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P090]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P090 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P090 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P090Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P090_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P090] using h

theorem momentScalarGrow2622K19P090_radius_le :
    (momentScalarGrow2622K19P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P090Expected]

end ConnesWeilRH.Dev
