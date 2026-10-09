import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K21
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K21P017 : ℚ := ((-6605611116373021407593340031015832353 : ℚ) / 102628992594477452345173091507240960)

def momentPanelGrowth2622K21P017 : ℚ := ((14920389851403800680351043520159026298643 : ℚ) / 7375441679886443756037554997430950297600)

theorem momentPanelPhase_owner2622K21P017 :
    (momentPanelPhase2622K21P017 : ℝ) = momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-29 / 40) 0 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K21P017 :
    (momentPanelGrowth2622K21P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K21P017Input : RatPair2542 := (momentPanelPhase2622K21P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K21P017Expected : RatState2542 :=
  ((((14878336071019788291797756346618438022417064644398528435683875045143 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2418153426259530387824275 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K21P017_replay :
    compactExp2620 momentScalarAmp2622K21P017Input 20 = momentScalarAmp2622K21P017Expected := by
  decide +kernel

theorem momentScalarAmp2622K21P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622K21P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K21P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K21P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P017]
  have h := compactExp_real_error2620 momentPanelPhase2622K21P017 20 hsmall
  change |Real.exp (momentPanelPhase2622K21P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K21P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K21P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K21P017_replay] at h
  simpa only [momentPanelPhase_owner2622K21P017] using h

theorem momentScalarAmp2622K21P017_radius_le :
    (momentScalarAmp2622K21P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarAmp2622K21P017Expected]

def momentScalarGrow2622K21P017Input : RatPair2542 := (momentPanelGrowth2622K21P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K21P017Expected : RatState2542 :=
  ((((16149860412220208853538713123510684688370757395853950718520845098732277392767216010976881754903113 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20472340748513685112366908850192198167759414138837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K21P017_replay :
    compactExp2620 momentScalarGrow2622K21P017Input 20 = momentScalarGrow2622K21P017Expected := by
  decide +kernel

theorem momentScalarGrow2622K21P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K21P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K21P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K21P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622K21P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622K21P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K21P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K21P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K21P017_replay] at h
  simpa only [momentPanelGrowth_owner2622K21P017] using h

theorem momentScalarGrow2622K21P017_radius_le :
    (momentScalarGrow2622K21P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarGrow2622K21P017Expected]

end ConnesWeilRH.Dev
