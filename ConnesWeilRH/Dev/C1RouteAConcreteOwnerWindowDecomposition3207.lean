import ConnesWeilRH.Dev.C1RouteAOwnerWeightedIntervalIntegrable3206
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584
import ConnesWeilRH.Dev.C1RouteAOwnerWindowDecomposition3202

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_weightedExternal_eq_ownerWindow3207
    (sigma : ℝ) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 sigma record2680CorrectionCoefficient
        capturedModulations2584 position) =
      ∫ position in (-(storedWidth 4 ^ 2))..(storedWidth 4 ^ 2),
        weightedExternal3201 sigma record2680CorrectionCoefficient
          capturedModulations2584 position := by
  apply intervalIntegral_weightedExternal_eq_ownerWindow3202 sigma
    record2680CorrectionCoefficient capturedModulations2584
  · exact weightedExternal3201_intervalIntegrable sigma
      record2680CorrectionCoefficient capturedModulations2584
      (-diagnosticRadius3201) (-(storedWidth 4 ^ 2))
  · exact weightedExternal3201_intervalIntegrable sigma
      record2680CorrectionCoefficient capturedModulations2584
      (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2)
  · exact weightedExternal3201_intervalIntegrable sigma
      record2680CorrectionCoefficient capturedModulations2584
      (storedWidth 4 ^ 2) diagnosticRadius3201

end ConnesWeilRH.Dev
