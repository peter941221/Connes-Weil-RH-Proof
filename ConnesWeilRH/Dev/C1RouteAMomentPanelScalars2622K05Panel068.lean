import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P068 : ℚ := ((-819122229256074387960955777557076838959 : ℚ) / 25793140292963829278133719460426547200)

def momentPanelGrowth2622K05P068 : ℚ := ((305882012169935672374255030745436029683 : ℚ) / 1913185949527012394164320753593981337600)

theorem momentPanelPhase_owner2622K05P068 :
    (momentPanelPhase2622K05P068 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-43 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P068 :
    (momentPanelGrowth2622K05P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P068Input : RatPair2542 := (momentPanelPhase2622K05P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P068Expected : RatState2542 :=
  ((((34478570273224200996762432443673613874629672323454402897605487396291138821538075795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((21854052017991832357245985004869807 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P068_replay :
    compactExp2620 momentScalarAmp2622K05P068Input 20 = momentScalarAmp2622K05P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K05P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P068_replay] at h
  simpa only [momentPanelPhase_owner2622K05P068] using h

theorem momentScalarAmp2622K05P068_radius_le :
    (momentScalarAmp2622K05P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P068Expected]

def momentScalarGrow2622K05P068Input : RatPair2542 := (momentPanelGrowth2622K05P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P068Expected : RatState2542 :=
  ((((2506305646299481550314920595043937666677885407347282771865370539369414198065436307923981729194477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3177119372457632397665460501079115497242204433613 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P068_replay :
    compactExp2620 momentScalarGrow2622K05P068Input 20 = momentScalarGrow2622K05P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P068] using h

theorem momentScalarGrow2622K05P068_radius_le :
    (momentScalarGrow2622K05P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P068Expected]

end ConnesWeilRH.Dev
