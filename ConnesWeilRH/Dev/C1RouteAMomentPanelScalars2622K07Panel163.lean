import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P163 : ℚ := ((-88501567421618022463668422678557677225 : ℚ) / 1492055180083031483067255593604481024)

def momentPanelGrowth2622K07P163 : ℚ := ((38918892777456711574274800848380401025 : ℚ) / 17296311567344449594111193268181008384)

theorem momentPanelPhase_owner2622K07P163 :
    (momentPanelPhase2622K07P163 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P163 :
    (momentPanelGrowth2622K07P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P163Input : RatPair2542 := (momentPanelPhase2622K07P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P163Expected : RatState2542 :=
  ((((37096240731123957710803996465729132134827650881855275165534285509247399 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2464879371219875243195405 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P163_replay :
    compactExp2620 momentScalarAmp2622K07P163Input 20 = momentScalarAmp2622K07P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K07P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P163_replay] at h
  simpa only [momentPanelPhase_owner2622K07P163] using h

theorem momentScalarAmp2622K07P163_radius_le :
    (momentScalarAmp2622K07P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P163Expected]

def momentScalarGrow2622K07P163Input : RatPair2542 := (momentPanelGrowth2622K07P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P163Expected : RatState2542 :=
  ((((20268248932345090584264914230669874449430778210511658804931705444385767462532717894881910532052419 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((25693002790295369203780478383286876284534740284049 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P163_replay :
    compactExp2620 momentScalarGrow2622K07P163Input 20 = momentScalarGrow2622K07P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P163] using h

theorem momentScalarGrow2622K07P163_radius_le :
    (momentScalarGrow2622K07P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P163Expected]

end ConnesWeilRH.Dev
