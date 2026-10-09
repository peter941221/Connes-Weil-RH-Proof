import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K07 : ℚ := ((27292010362673683961057012550625 : ℚ) / 5070602400912917605986812821504)
def momentBeta2620K07 : ℚ := ((81876031088021051883171037651875 : ℚ) / 10141204801825835211973625643008)
def momentPanelPhase2620K07 : ℚ := ((-96178938754927041581702056498147728675 : ℚ) / 3238614035872684126614201296345890816)
def momentPanelGrowth2620K07 : ℚ := ((238700324401605871768000702318133225 : ℚ) / 2152653260873966388775217567990022144)
def momentEdgeArgument2620K07 : ℚ := ((-28867969814805105650140627213638375 : ℚ) / 192682891234690869027498887217152)

theorem momentRadius_owner2620K07 :
    (momentRadius2620K07 : ℝ) = storedWidth 7 ^ 2 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentRadius2620K07, storedWidth]

theorem momentBeta_owner2620K07 :
    (momentBeta2620K07 : ℝ) = (capturedNodes2584 7).re * (storedWidth 7 ^ 2) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentBeta2620K07, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K07 :
    (momentPanelPhase2620K07 : ℝ) = momentPhase2619
      ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2620K07, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K07 :
    (momentPanelGrowth2620K07 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2620K07, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K07 :
    (momentEdgeArgument2620K07 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 7).re * (storedWidth 7 ^ 2)| := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentEdgeArgument2620K07, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
