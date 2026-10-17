import ConnesWeilRH.Dev.C1RepairedOwnerCellChargeUpper2780

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2686RepairedOwnerCellIntegralTotal_lt_10000_2791 :
    (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2678BaseCoefficient capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2678BaseCoefficient
            capturedModulations2584)) x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2680CorrectionCoefficient
            capturedModulations2584)) x‖) < 10000 := by
  calc
    _ ≤ (binary64Value2674 0x40c1696a1ea9e753 : ℝ) :=
      record2686RepairedOwnerCellCharge
    _ < 10000 := by
      exact_mod_cast record2686RepairedOwnerCellCharge_constant_lt_10000_2790

end ConnesWeilRH.Dev
