import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P066 : ℚ := ((-34390873009440378916591536512870858425 : ℚ) / 1021990055108800369321854097799774208)

def momentPanelGrowth2622K07P066 : ℚ := ((3417951663654306976308528951805845075 : ℚ) / 14072787644216882310292408726791913472)

theorem momentPanelPhase_owner2622K07P066 :
    (momentPanelPhase2622K07P066 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P066 :
    (momentPanelGrowth2622K07P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P066Input : RatPair2542 := (momentPanelPhase2622K07P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P066Expected : RatState2542 :=
  ((((5190432990581768198697153897571870201619491892080772844348702374108594548938111257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((822483331998111031313020809319691 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P066_replay :
    compactExp2620 momentScalarAmp2622K07P066Input 20 = momentScalarAmp2622K07P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K07P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P066_replay] at h
  simpa only [momentPanelPhase_owner2622K07P066] using h

theorem momentScalarAmp2622K07P066_radius_le :
    (momentScalarAmp2622K07P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P066Expected]

def momentScalarGrow2622K07P066Input : RatPair2542 := (momentPanelGrowth2622K07P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P066Expected : RatState2542 :=
  ((((2723194152268657644757960249435566975228772933589747938417808387925956841248513763126913574531917 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3452057902077559933867847130657876103277269004983 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P066_replay :
    compactExp2620 momentScalarGrow2622K07P066Input 20 = momentScalarGrow2622K07P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P066] using h

theorem momentScalarGrow2622K07P066_radius_le :
    (momentScalarGrow2622K07P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P066Expected]

end ConnesWeilRH.Dev
