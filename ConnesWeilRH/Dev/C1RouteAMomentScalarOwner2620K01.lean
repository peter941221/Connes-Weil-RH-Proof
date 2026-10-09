import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620K01 : ℚ := ((268234867008293299923585826449 : ℚ) / 79228162514264337593543950336)
def momentBeta2620K01 : ℚ := ((66441234590847759014363306679944080784316273 : ℚ) / 356811923176489970264571492362373784095686656)
def momentPanelPhase2620K01 : ℚ := ((-85610991153564904398268308847415497993117335348283017 : ℚ) / 2848715032256460624598285880722719817463143124172800)
def momentPanelGrowth2620K01 : ℚ := ((60615744704270913269946656373564397990291176619291 : ℚ) / 1893493832720679325203001538519408960060580377395200)
def momentEdgeArgument2620K01 : ℚ := ((-1069173386072243803372441574260202414752157958813 : ℚ) / 6779426540353309435026858354885101897818046464)

theorem momentRadius_owner2620K01 :
    (momentRadius2620K01 : ℝ) = storedWidth 1 ^ 2 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentRadius2620K01, storedWidth]

theorem momentBeta_owner2620K01 :
    (momentBeta2620K01 : ℝ) = (capturedNodes2584 1).re * (storedWidth 1 ^ 2) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentBeta2620K01, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620K01 :
    (momentPanelPhase2620K01 : ℝ) = momentPhase2619
      ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2620K01, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620K01 :
    (momentPanelGrowth2620K01 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2620K01, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620K01 :
    (momentEdgeArgument2620K01 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 1).re * (storedWidth 1 ^ 2)| := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentEdgeArgument2620K01, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
