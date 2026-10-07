import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentRadius2620 : ℚ := ((12980742146337070512478121581609 : ℚ) / 5070602400912917605986812821504)
def momentBeta2620 : ℚ := ((55244761891108140076107751795320548074582996471 : ℚ) / 22835963083295358096932575511191922182123945984)
def momentPanelPhase2620 : ℚ := ((-5460783299141505630670534814590804715082443528434867359 : ℚ) / 182317762064413479974290296366254068317641159947059200)
def momentPanelGrowth2620 : ℚ := ((6585427872602692964928022146312983073813727231166557 : ℚ) / 121183605294123476812992098465242173443877144153292800)
def momentEdgeArgument2620 : ℚ := ((-67458238773955019629351679249464676132954761019051 : ℚ) / 433883298582611803841718934712646521460354973696)

theorem momentRadius_owner2620 :
    (momentRadius2620 : ℝ) = storedWidth 0 ^ 2 := by
  norm_num [momentRadius2620, storedWidth]

theorem momentBeta_owner2620 :
    (momentBeta2620 : ℝ) = (capturedNodes2584 0).re * (storedWidth 0 ^ 2) := by
  norm_num [momentBeta2620, capturedNodes2584, storedWidth]

theorem momentPanelPhase_owner2620 :
    (momentPanelPhase2620 : ℝ) = momentPhase2619
      ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) 0 := by
  norm_num [momentPanelPhase2620, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2620 :
    (momentPanelGrowth2620 : ℝ) = 2 * momentPhaseSlopeUpper2619
      ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2620, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

theorem momentEdgeArgument_owner2620 :
    (momentEdgeArgument2620 : ℝ) = -30 / (1 - (9 / 10 : ℝ) ^ 2) +
      |(capturedNodes2584 0).re * (storedWidth 0 ^ 2)| := by
  norm_num [momentEdgeArgument2620, capturedNodes2584, storedWidth]

end ConnesWeilRH.Dev
