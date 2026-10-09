import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K03 : ℚ := ((27292010362673683961057012550625 : ℚ) / 5070602400912917605986812821504)
def momentBeta2620K03 : ℚ := ((6760175823474082874695475091754557518672210625 : ℚ) / 22835963083295358096932575511191922182123945984)
def momentPanelPhase2620K03 : ℚ := ((-219128096194504423441413736186174862883018246095061825 : ℚ) / 7292710482576539198971611854650162732705646397882368)
def momentPanelGrowth2620K03 : ℚ := ((160499853750062258056827074339393866119328382347075 : ℚ) / 4847344211764939072519683938609686937755085766131712)
def momentEdgeArgument2620K03 : ℚ := ((-68379445909240066716178512506832429953517065950125 : ℚ) / 433883298582611803841718934712646521460354973696)

theorem momentRadius_owner2620K03 :
    (momentRadius2620K03 : ℝ) = storedWidth 3 ^ 2 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentRadius2620K03, storedWidth]

theorem momentBeta_owner2620K03 :
    (momentBeta2620K03 : ℝ) = (capturedNodes2584 3).re * (storedWidth 3 ^ 2) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentBeta2620K03, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K03 :
    (momentPanelPhase2620K03 : ℝ) = momentPhase2619
      ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2620K03, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K03 :
    (momentPanelGrowth2620K03 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2620K03, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K03 :
    (momentEdgeArgument2620K03 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 3).re * (storedWidth 3 ^ 2)| := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentEdgeArgument2620K03, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
