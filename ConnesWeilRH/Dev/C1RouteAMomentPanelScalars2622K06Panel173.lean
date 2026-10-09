import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P173 : ℚ := ((-19325821 : ℚ) / 201850)

def momentPanelGrowth2622K06P173 : ℚ := ((4955731 : ℚ) / 846400)

theorem momentPanelPhase_owner2622K06P173 :
    (momentPanelPhase2622K06P173 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P173 :
    (momentPanelGrowth2622K06P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P173Input : RatPair2542 := (momentPanelPhase2622K06P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P173Expected : RatState2542 :=
  ((((5607051081632420587015198091388275272027667310092466433 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629178264309 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P173_replay :
    compactExp2620 momentScalarAmp2622K06P173Input 20 = momentScalarAmp2622K06P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K06P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P173_replay] at h
  simpa only [momentPanelPhase_owner2622K06P173] using h

theorem momentScalarAmp2622K06P173_radius_le :
    (momentScalarAmp2622K06P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P173Expected]

def momentScalarGrow2622K06P173Input : RatPair2542 := (momentPanelGrowth2622K06P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P173Expected : RatState2542 :=
  ((((372728912095179769246645610840206130313876869028378291279842097240092656180608183383373951254307415 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((944974781686849862627563090477595189282335930595523 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P173_replay :
    compactExp2620 momentScalarGrow2622K06P173Input 20 = momentScalarGrow2622K06P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P173] using h

theorem momentScalarGrow2622K06P173_radius_le :
    (momentScalarGrow2622K06P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P173Expected]

end ConnesWeilRH.Dev
