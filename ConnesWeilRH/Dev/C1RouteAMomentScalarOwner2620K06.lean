import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K06 : ℚ := ((4 : ℚ) / 1)
def momentBeta2620K06 : ℚ := ((4 : ℚ) / 1)
def momentPanelPhase2620K06 : ℚ := ((-59640729 : ℚ) / 1995950)
def momentPanelGrowth2620K06 : ℚ := ((93067 : ℚ) / 1326675)
def momentEdgeArgument2620K06 : ℚ := ((-2924 : ℚ) / 19)

theorem momentRadius_owner2620K06 :
    (momentRadius2620K06 : ℝ) = storedWidth 6 ^ 2 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentRadius2620K06, storedWidth]

theorem momentBeta_owner2620K06 :
    (momentBeta2620K06 : ℝ) = (capturedNodes2584 6).re * (storedWidth 6 ^ 2) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentBeta2620K06, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K06 :
    (momentPanelPhase2620K06 : ℝ) = momentPhase2619
      ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2620K06, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K06 :
    (momentPanelGrowth2620K06 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2620K06, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K06 :
    (momentEdgeArgument2620K06 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 6).re * (storedWidth 6 ^ 2)| := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentEdgeArgument2620K06, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
