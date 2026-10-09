import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P073 : ℚ := ((-101560925381807121072717216257691982725 : ℚ) / 3156835360350760591464845979160674304)

def momentPanelGrowth2622K07P073 : ℚ := ((240869692199575973745597435355513930025 : ℚ) / 1275135093325711319006525676362057908224)

theorem momentPanelPhase_owner2622K07P073 :
    (momentPanelPhase2622K07P073 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P073 :
    (momentPanelGrowth2622K07P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P073Input : RatPair2542 := (momentPanelPhase2622K07P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P073Expected : RatState2542 :=
  ((((22781593554815272964343126598975631661890984840813842054451023412053735041537637831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((28879986810416084851756673591387347 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P073_replay :
    compactExp2620 momentScalarAmp2622K07P073Input 20 = momentScalarAmp2622K07P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K07P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P073_replay] at h
  simpa only [momentPanelPhase_owner2622K07P073] using h

theorem momentScalarAmp2622K07P073_radius_le :
    (momentScalarAmp2622K07P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P073Expected]

def momentScalarGrow2622K07P073Input : RatPair2542 := (momentPanelGrowth2622K07P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P073Expected : RatState2542 :=
  ((((2580095058601494244874686797092267911380679433064412977765362318717325798359034320653589384565485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3270658460484050659238322502774989397267394838185 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P073_replay :
    compactExp2620 momentScalarGrow2622K07P073Input 20 = momentScalarGrow2622K07P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P073] using h

theorem momentScalarGrow2622K07P073_radius_le :
    (momentScalarGrow2622K07P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P073Expected]

end ConnesWeilRH.Dev
