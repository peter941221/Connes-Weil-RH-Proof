import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P147 : ℚ := ((-6372861249844194537553699626781638221 : ℚ) / 144816404570072926826983374182154240)

def momentPanelGrowth2622K05P147 : ℚ := ((748366891998282110406211301120863858003 : ℚ) / 930381509772467052101532745278790041600)

theorem momentPanelPhase_owner2622K05P147 :
    (momentPanelPhase2622K05P147 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P147 :
    (momentPanelGrowth2622K05P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P147Input : RatPair2542 := (momentPanelPhase2622K05P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P147Expected : RatState2542 :=
  ((((165129271990633664059985959757109196427968771505195901707124474622857820095489 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((209337423762972685798703526599 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P147_replay :
    compactExp2620 momentScalarAmp2622K05P147Input 20 = momentScalarAmp2622K05P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K05P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P147_replay] at h
  simpa only [momentPanelPhase_owner2622K05P147] using h

theorem momentScalarAmp2622K05P147_radius_le :
    (momentScalarAmp2622K05P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P147Expected]

def momentScalarGrow2622K05P147Input : RatPair2542 := (momentPanelGrowth2622K05P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P147Expected : RatState2542 :=
  ((((4774524859955181271810039784884572917812873522277076140177155559472166271763907945260425143656433 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6052424661692953852539050906438124336001895074225 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P147_replay :
    compactExp2620 momentScalarGrow2622K05P147Input 20 = momentScalarGrow2622K05P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P147] using h

theorem momentScalarGrow2622K05P147_radius_le :
    (momentScalarGrow2622K05P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P147Expected]

end ConnesWeilRH.Dev
