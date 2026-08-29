/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger

/-!
# C1 metric-projection response guard

The active response is exactly the difference between the archimedean Sonin
projection and the Gram-corrected projection onto its finite-Euler transport.
This small readback keeps that endpoint-metric identity explicit.  It does not
assert a trace formula or a sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1MetricProjectionResponseGuard

open CC20Concrete
open CCM25Concrete.SelectedWeilSquare
open C1Stage3ProjectionTraceLedger

noncomputable section

/-- The C1 Sonin band is exactly the source metric projection minus the
Gram-corrected finite-Euler target projection. -/
theorem soninBandDifference_eq_metricProjectionDifference
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    soninBandDifference lambda S =
      sourceSoninProjection lambda - targetSoninProjection lambda S := by
  simp only [soninBandDifference]
  abel

/-- The C1 projection response is therefore a detector applied to the endpoint
metric-projection difference. -/
theorem projectionResponse_eq_metricProjectionResponse
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime) :
    projectionResponse owner lambda S =
      detectorOperator owner ∘L
        (sourceSoninProjection lambda - targetSoninProjection lambda S) := by
  rw [projectionResponse, soninBandDifference_eq_metricProjectionDifference]

end
end C1MetricProjectionResponseGuard
end Source
end ConnesWeilRH
