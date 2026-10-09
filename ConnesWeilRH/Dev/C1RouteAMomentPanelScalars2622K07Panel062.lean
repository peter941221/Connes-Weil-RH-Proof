import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P062 : ℚ := ((-1386876957951774540005111389742247625 : ℚ) / 39996911738401094076023979536023552)

def momentPanelGrowth2622K07P062 : ℚ := ((305065620450004284141171459864025 : ℚ) / 1095250118597190202893151569444864)

theorem momentPanelPhase_owner2622K07P062 :
    (momentPanelPhase2622K07P062 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P062 :
    (momentPanelGrowth2622K07P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P062Input : RatPair2542 := (momentPanelPhase2622K07P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P062Expected : RatState2542 :=
  ((((1864707476809631766729254800665461143711216642551302318159835294698988538551879755 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1181937861324514462313450896835651 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P062_replay :
    compactExp2620 momentScalarAmp2622K07P062Input 20 = momentScalarAmp2622K07P062Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622K07P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P062]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P062 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P062_replay] at h
  simpa only [momentPanelPhase_owner2622K07P062] using h

theorem momentScalarAmp2622K07P062_radius_le :
    (momentScalarAmp2622K07P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P062Expected]

def momentScalarGrow2622K07P062Input : RatPair2542 := (momentPanelGrowth2622K07P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P062Expected : RatState2542 :=
  ((((2822051123251635652800531738051469596468968045579085605145070251862305309554080799346152129228383 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3577373850000347538778601193434110095140231100173 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P062_replay :
    compactExp2620 momentScalarGrow2622K07P062Input 20 = momentScalarGrow2622K07P062Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P062_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P062] using h

theorem momentScalarGrow2622K07P062_radius_le :
    (momentScalarGrow2622K07P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P062Expected]

end ConnesWeilRH.Dev
