/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3GateAmbientNormalForm

/-!
# Direct source-gate consumer for the G8 S3 obligation

The gate normal form already contains two unconditional equivalences: the
source-compressed gate is equivalent to the Hardy-compressed root energy, and
that energy is equivalent to the source-projection root energy after removing
the square-summable prolate remainder.  This leaf composes them into the
single source-facing target consumed by the healthy-`CompactLog` B5 route.

No estimate, sign, carrier-existence claim, or RH conclusion is introduced.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceGateBridgeCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
/-- The source-compressed G8 gate is exactly the source-projection root
square-sum.  The prolate remainder is already absorbed by the imported
gate-normal-form equivalences; the remaining analytic producer is therefore
the displayed source-projection square-sum itself. -/
theorem sourceGate_squareSum_iff_sourceProjectionRootEnergy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) ↔
    (Summable fun i : ρ =>
      ‖(sourceSoninProjection lambda ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) := by
  exact (sourceGate_squareSum_iff_hardyCompressedRootEnergy owner lambda
    sourceBasis).trans
    (hardyCompressedRootEnergy_squareSum_iff_sourceProjectionRootEnergy
      owner lambda sourceBasis)

end Dev
end ConnesWeilRH
