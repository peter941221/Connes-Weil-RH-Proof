import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P110 : ℚ := ((-19476307 : ℚ) / 638650)

def momentPanelGrowth2622K06P110 : ℚ := ((406374481 : ℚ) / 2284362025)

theorem momentPanelPhase_owner2622K06P110 :
    (momentPanelPhase2622K06P110 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (41 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P110, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P110 :
    (momentPanelGrowth2622K06P110 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P110, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P110Input : RatPair2542 := (momentPanelPhase2622K06P110 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P110Expected : RatState2542 :=
  ((((60855412135399499563010228298430740623551607104769085029424158848706685587351772421 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((77145643339556886247846321731501403 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P110_replay :
    compactExp2620 momentScalarAmp2622K06P110Input 20 = momentScalarAmp2622K06P110Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P110_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (41 / 200) 0) -
      (momentScalarAmp2622K06P110Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P110]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P110 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P110 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P110Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P110_replay] at h
  simpa only [momentPanelPhase_owner2622K06P110] using h

theorem momentScalarAmp2622K06P110_radius_le :
    (momentScalarAmp2622K06P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P110Expected]

def momentScalarGrow2622K06P110Input : RatPair2542 := (momentPanelGrowth2622K06P110 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P110Expected : RatState2542 :=
  ((((637965272275516539949800267052659736823033165441623759949508252672274275991551712162971632239045 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3234867692494193027872171931494398101313839876307 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P110_replay :
    compactExp2620 momentScalarGrow2622K06P110Input 20 = momentScalarGrow2622K06P110Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P110_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P110Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P110]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P110 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P110 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P110Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P110_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P110] using h

theorem momentScalarGrow2622K06P110_radius_le :
    (momentScalarGrow2622K06P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P110Expected]

end ConnesWeilRH.Dev
