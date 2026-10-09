import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K15
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K15P162 : ℚ := ((-6375131029964047663732900792034407647 : ℚ) / 102628992594477452345173091507240960)

def momentPanelGrowth2622K15P162 : ℚ := ((14920389851403800680351043520159026298643 : ℚ) / 7375441679886443756037554997430950297600)

theorem momentPanelPhase_owner2622K15P162 :
    (momentPanelPhase2622K15P162 : ℝ) = momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K15P162 :
    (momentPanelGrowth2622K15P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K15P162Input : RatPair2542 := (momentPanelPhase2622K15P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K15P162Expected : RatState2542 :=
  ((((2249031419308522665769246450083649921736994652307292692204673704372061 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302587849269629765908175 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K15P162_replay :
    compactExp2620 momentScalarAmp2622K15P162Input 20 = momentScalarAmp2622K15P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K15P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K15P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K15P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K15P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K15P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K15P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K15P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K15P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K15P162_replay] at h
  simpa only [momentPanelPhase_owner2622K15P162] using h

theorem momentScalarAmp2622K15P162_radius_le :
    (momentScalarAmp2622K15P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarAmp2622K15P162Expected]

def momentScalarGrow2622K15P162Input : RatPair2542 := (momentPanelGrowth2622K15P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K15P162Expected : RatState2542 :=
  ((((16149860412220208853538713123510684688370757395853950718520845098732277392767216010976881754903113 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20472340748513685112366908850192198167759414138837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K15P162_replay :
    compactExp2620 momentScalarGrow2622K15P162Input 20 = momentScalarGrow2622K15P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K15P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K15P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K15P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K15P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K15P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K15P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K15P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K15P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K15P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K15P162] using h

theorem momentScalarGrow2622K15P162_radius_le :
    (momentScalarGrow2622K15P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarGrow2622K15P162Expected]

end ConnesWeilRH.Dev
