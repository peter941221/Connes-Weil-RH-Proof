import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P112 : ℚ := ((-466329 : ℚ) / 15190)

def momentPanelGrowth2622K06P112 : ℚ := ((144899947 : ℚ) / 747498675)

theorem momentPanelPhase_owner2622K06P112 :
    (momentPanelPhase2622K06P112 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P112 :
    (momentPanelGrowth2622K06P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P112Input : RatPair2542 := (momentPanelPhase2622K06P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P112Expected : RatState2542 :=
  ((((49641213062902745786713997648553260437834059939474367230168945577257958922347340235 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((62929555932728731091653356455406787 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P112_replay :
    compactExp2620 momentScalarAmp2622K06P112Input 20 = momentScalarAmp2622K06P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K06P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P112_replay] at h
  simpa only [momentPanelPhase_owner2622K06P112] using h

theorem momentScalarAmp2622K06P112_radius_le :
    (momentScalarAmp2622K06P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P112Expected]

def momentScalarGrow2622K06P112Input : RatPair2542 := (momentPanelGrowth2622K06P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P112Expected : RatState2542 :=
  ((((2592895690240957726379340173540364140112253599390648636092483485364601778833801528307696863181815 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3286885170428591433271927519892981686706055029533 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P112_replay :
    compactExp2620 momentScalarGrow2622K06P112Input 20 = momentScalarGrow2622K06P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P112] using h

theorem momentScalarGrow2622K06P112_radius_le :
    (momentScalarGrow2622K06P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P112Expected]

end ConnesWeilRH.Dev
