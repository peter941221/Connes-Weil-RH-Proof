import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P040 : ℚ := ((-2480847483146732222101235852374394064669 : ℚ) / 61250848762067679513278304158639718400)

def momentPanelGrowth2622K20P040 : ℚ := ((1669712862283337207009777493977387 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K20P040 :
    (momentPanelPhase2622K20P040 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P040 :
    (momentPanelGrowth2622K20P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P040Input : RatPair2542 := (momentPanelPhase2622K20P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P040Expected : RatState2542 :=
  ((((5487042549034496738730738120237685388688670007992836756696062910653987928692863 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3477961938992138244397755282409 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K20P040_replay :
    compactExp2620 momentScalarAmp2622K20P040Input 20 = momentScalarAmp2622K20P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K20P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P040_replay] at h
  simpa only [momentPanelPhase_owner2622K20P040] using h

theorem momentScalarAmp2622K20P040_radius_le :
    (momentScalarAmp2622K20P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P040Expected]

def momentScalarGrow2622K20P040Input : RatPair2542 := (momentPanelGrowth2622K20P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P040Expected : RatState2542 :=
  ((((3697844880002555292408840920053074995782381595952380034368606535913561506739888926930181938033431 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4687572828224817715415424978055226954461070800823 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P040_replay :
    compactExp2620 momentScalarGrow2622K20P040Input 20 = momentScalarGrow2622K20P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P040] using h

theorem momentScalarGrow2622K20P040_radius_le :
    (momentScalarGrow2622K20P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P040Expected]

end ConnesWeilRH.Dev
