import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P122 : ℚ := ((-153799 : ℚ) / 4770)

def momentPanelGrowth2622K06P122 : ℚ := ((574405921 : ℚ) / 1985148025)

theorem momentPanelPhase_owner2622K06P122 :
    (momentPanelPhase2622K06P122 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P122 :
    (momentPanelGrowth2622K06P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P122Input : RatPair2542 := (momentPanelPhase2622K06P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P122Expected : RatState2542 :=
  ((((21215420672314518686481158847055456518655219743823086759753088698855868979575408543 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26894567728161444368416556326355521 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P122_replay :
    compactExp2620 momentScalarAmp2622K06P122Input 20 = momentScalarAmp2622K06P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K06P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P122_replay] at h
  simpa only [momentPanelPhase_owner2622K06P122] using h

theorem momentScalarAmp2622K06P122_radius_le :
    (momentScalarAmp2622K06P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P122Expected]

def momentScalarGrow2622K06P122Input : RatPair2542 := (momentPanelGrowth2622K06P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P122Expected : RatState2542 :=
  ((((2852741706778652309159235582954998439986100906322054604573443631687335709470160015804359130840901 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1808139369495843138506473750316450817330811714459 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P122_replay :
    compactExp2620 momentScalarGrow2622K06P122Input 20 = momentScalarGrow2622K06P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P122] using h

theorem momentScalarGrow2622K06P122_radius_le :
    (momentScalarGrow2622K06P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P122Expected]

end ConnesWeilRH.Dev
