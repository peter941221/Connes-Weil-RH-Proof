import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K02 : ℚ := ((1371090889206853014333706436241 : ℚ) / 316912650057057350374175801344)
def momentBeta2620K02 : ℚ := ((5835227974748297046369479302519934167341377679 : ℚ) / 1427247692705959881058285969449495136382746624)
def momentPanelPhase2620K02 : ℚ := ((-340443018059714576025842423469383193463624285659887991 : ℚ) / 11394860129025842498393143522890879269852572496691200)
def momentPanelGrowth2620K02 : ℚ := ((538017673768921460329014913258744568279544349131493 : ℚ) / 7573975330882717300812006154077635840242321509580800)
def momentEdgeArgument2620K02 : ℚ := ((-4170873746597661999293837801600606659968753696099 : ℚ) / 27117706161413237740107433419540407591272185856)

theorem momentRadius_owner2620K02 :
    (momentRadius2620K02 : ℝ) = storedWidth 2 ^ 2 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentRadius2620K02, storedWidth]

theorem momentBeta_owner2620K02 :
    (momentBeta2620K02 : ℝ) = (capturedNodes2584 2).re * (storedWidth 2 ^ 2) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentBeta2620K02, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K02 :
    (momentPanelPhase2620K02 : ℝ) = momentPhase2619
      ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2620K02, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K02 :
    (momentPanelGrowth2620K02 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2620K02, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K02 :
    (momentEdgeArgument2620K02 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 2).re * (storedWidth 2 ^ 2)| := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentEdgeArgument2620K02, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
