import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P138 : ℚ := ((-795760747796885025298079829604080233779 : ℚ) / 20681973072843608331299012136350515200)

def momentPanelGrowth2622K20P138 : ℚ := ((10240707422525245849823245757188270065523 : ℚ) / 19520061772722576365806994333466466713600)

theorem momentPanelPhase_owner2622K20P138 :
    (momentPanelPhase2622K20P138 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P138 :
    (momentPanelGrowth2622K20P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P138Input : RatPair2542 := (momentPanelPhase2622K20P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P138Expected : RatState2542 :=
  ((((10413577372457069223488317319297123197125564179386215344301789766587829986852199 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((52805050417864498965673367211889 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P138_replay :
    compactExp2620 momentScalarAmp2622K20P138Input 20 = momentScalarAmp2622K20P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K20P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P138_replay] at h
  simpa only [momentPanelPhase_owner2622K20P138] using h

theorem momentScalarAmp2622K20P138_radius_le :
    (momentScalarAmp2622K20P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P138Expected]

def momentScalarGrow2622K20P138Input : RatPair2542 := (momentPanelGrowth2622K20P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P138Expected : RatState2542 :=
  ((((902360866914265598787782160577863962885646030155137544797916305691664746524325828025575443706749 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2287755444519959346788635866540175069430613252389 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K20P138_replay :
    compactExp2620 momentScalarGrow2622K20P138Input 20 = momentScalarGrow2622K20P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P138] using h

theorem momentScalarGrow2622K20P138_radius_le :
    (momentScalarGrow2622K20P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P138Expected]

end ConnesWeilRH.Dev
