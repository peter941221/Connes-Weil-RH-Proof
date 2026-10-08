import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K04 : ℚ := ((2076918743413931858457251756481 : ℚ) / 316912650057057350374175801344)
def momentBeta2620K04 : ℚ := ((13515967142036196021093197896839762196200178527 : ℚ) / 1427247692705959881058285969449495136382746624)
def momentPanelPhase2620K04 : ℚ := ((-337683551218343885273294458366283314527868155420426183 : ℚ) / 11394860129025842498393143522890879269852572496691200)
def momentPanelGrowth2620K04 : ℚ := ((945611459159388395220678487903514882286994333732309 : ℚ) / 7573975330882717300812006154077635840242321509580800)
def momentEdgeArgument2620K04 : ℚ := ((-4024939702419191918774087148308529927420436479987 : ℚ) / 27117706161413237740107433419540407591272185856)

theorem momentRadius_owner2620K04 :
    (momentRadius2620K04 : ℝ) = storedWidth 4 ^ 2 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentRadius2620K04, storedWidth]

theorem momentBeta_owner2620K04 :
    (momentBeta2620K04 : ℝ) = (capturedNodes2584 4).re * (storedWidth 4 ^ 2) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentBeta2620K04, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K04 :
    (momentPanelPhase2620K04 : ℝ) = momentPhase2619
      ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2620K04, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K04 :
    (momentPanelGrowth2620K04 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2620K04, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K04 :
    (momentEdgeArgument2620K04 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 4).re * (storedWidth 4 ^ 2)| := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentEdgeArgument2620K04, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
