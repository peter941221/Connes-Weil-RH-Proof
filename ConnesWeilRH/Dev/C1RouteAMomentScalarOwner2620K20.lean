import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K20 : ℚ := ((15706697997067857697999130365369 : ℚ) / 5070602400912917605986812821504)
def momentBeta2620K20 : ℚ := ((15706697997067857697999130365369 : ℚ) / 10141204801825835211973625643008)
def momentPanelPhase2620K20 : ℚ := ((-2428246191342095884570652308756423514001 : ℚ) / 80965350896817103165355032408647270400)
def momentPanelGrowth2620K20 : ℚ := ((2456100110902533638375499953980316723 : ℚ) / 53816331521849159719380439199750553600)
def momentEdgeArgument2620K20 : ℚ := ((-30125187143533216339658893452081989 : ℚ) / 192682891234690869027498887217152)

theorem momentRadius_owner2620K20 :
    (momentRadius2620K20 : ℝ) = storedWidth 20 ^ 2 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentRadius2620K20, storedWidth]

theorem momentBeta_owner2620K20 :
    (momentBeta2620K20 : ℝ) = (capturedNodes2584 20).re * (storedWidth 20 ^ 2) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentBeta2620K20, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K20 :
    (momentPanelPhase2620K20 : ℝ) = momentPhase2619
      ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2620K20, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K20 :
    (momentPanelGrowth2620K20 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2620K20, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K20 :
    (momentEdgeArgument2620K20 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 20).re * (storedWidth 20 ^ 2)| := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentEdgeArgument2620K20, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
