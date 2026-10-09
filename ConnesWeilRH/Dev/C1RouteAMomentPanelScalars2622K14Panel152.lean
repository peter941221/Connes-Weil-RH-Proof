import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P152 : ℚ := ((-50902033215538865534935019818451975 : ℚ) / 1054685299389886862045257066872832)

def momentPanelGrowth2622K14P152 : ℚ := ((38905053264587784403663177077383722387609 : ℚ) / 36886564674982383295754341854172990668800)

theorem momentPanelPhase_owner2622K14P152 :
    (momentPanelPhase2622K14P152 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (5 / 8) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P152 :
    (momentPanelGrowth2622K14P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P152Input : RatPair2542 := (momentPanelPhase2622K14P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P152Expected : RatState2542 :=
  ((((2340691910381849523499103760854682805393997749171250547571949663227043838735 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1484866965094976095617554473 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K14P152_replay :
    compactExp2620 momentScalarAmp2622K14P152Input 20 = momentScalarAmp2622K14P152Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622K14P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P152]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P152 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P152_replay] at h
  simpa only [momentPanelPhase_owner2622K14P152] using h

theorem momentScalarAmp2622K14P152_radius_le :
    (momentScalarAmp2622K14P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P152Expected]

def momentScalarGrow2622K14P152Input : RatPair2542 := (momentPanelGrowth2622K14P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P152Expected : RatState2542 :=
  ((((6132793548657019267831800516463194005489283384942448893432116347484745247776543911954938894366009 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7774231603231999554042028515183339969660632330781 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K14P152_replay :
    compactExp2620 momentScalarGrow2622K14P152Input 20 = momentScalarGrow2622K14P152Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P152_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P152] using h

theorem momentScalarGrow2622K14P152_radius_le :
    (momentScalarGrow2622K14P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P152Expected]

end ConnesWeilRH.Dev
