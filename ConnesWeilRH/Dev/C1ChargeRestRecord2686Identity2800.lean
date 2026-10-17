import ConnesWeilRH.Dev.C1ChargeRestRepairedOwnerBridge2793

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2686RepairedOwnerTotal2800 : ℝ :=
    (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2678BaseCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2678BaseCoefficient
            capturedModulations2584)) x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2680CorrectionCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2680CorrectionCoefficient
            capturedModulations2584)) x‖)

theorem record2686RepairedOwnerTotal_lt_10000_2800 :
    record2686RepairedOwnerTotal2800 < 10000 := by
  simpa [record2686RepairedOwnerTotal2800] using
    record2686RepairedOwnerCellIntegralTotal_lt_10000_2791

theorem chargeRest_le_knownError_of_record2686_total_identity2800
    {chargeRest : ℝ}
    (hidentity : chargeRest = record2686RepairedOwnerTotal2800) :
    chargeRest ≤ knownError2109 := by
  apply chargeRest_le_knownError_of_repaired_owner_identity2793
    (chargeRest := chargeRest)
    (repairedTotal := record2686RepairedOwnerTotal2800)
  · exact hidentity
  · exact record2686RepairedOwnerTotal_lt_10000_2800

end ConnesWeilRH.Dev
