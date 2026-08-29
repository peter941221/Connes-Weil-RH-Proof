/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionDefectBounds

/-!
# C1 projection-square canonical-cutoff guard

The canonical Stage-3 finite-window bridge has a named second defect
`D2 = windowedDetector - projectionResponse`. For a nonzero source test, its
real trace cannot converge to zero along the canonical cutoff. This records
the rejection as an import-facing theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1ProjectionSquareCanonicalCutoffGuard

open CC20Concrete
open CC20Concrete.PositiveTrace
open C1Stage3ProjectionDefectBounds
open C1Stage3ProjectionResponseBridge
open C1Stage3ProjectionTraceLedger
open CCM25Concrete.SelectedWeilSquare
open Filter
open scoped Topology

noncomputable section

/-- The canonical cutoff cannot close the projection-square trace ledger by
declaring its window-to-response defect to tend to zero. -/
theorem canonicalCutoffWindowToResponseDefect_not_tendsto_zero
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu Complex cc20GlobalLogCrossingL2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S))
    (hg : Not (owner.sourceTest.test = 0)) :
    Not (Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S n)).re)
      atTop (nhds (0 : Real))) := by
  exact not_tendsto_zero_cutoffWindowToResponseDefect_trace_re_of_sourceTest_ne_zero
    owner lambda S globalBasis hresponse hg

end

end C1ProjectionSquareCanonicalCutoffGuard
end Dev
end Source
end ConnesWeilRH
