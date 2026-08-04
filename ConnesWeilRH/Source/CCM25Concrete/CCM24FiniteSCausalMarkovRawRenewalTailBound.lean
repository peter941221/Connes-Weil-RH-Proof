/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawRenewalSupportSplit

/-!
# Raw renewal tail trace bound contract

Physical Gate 3U reduces exactly to a bound on the ordinary trace of the raw
source-band endpoint.  Proof 807 splits that complete physical renewal owner
into a compact-displacement part and a complementary tail at operator level:

```text
R_T = R_T^(<= B) + R_T^(> B)
```

This module records the trace-level consequence: taking the real ordinary trace
preserves the split exactly (using `ordinaryTraceAlong_add`), so the Gate bound
splits as a compact part plus a tail part.  A producer who supplies a uniform
tail-decay bound for `R^(> B)` therefore closes the canonical real Gate via the
already declared lower-factor persistence consumer, with compact root support
applied before any absolute value.

No new analytic claim is introduced here; this is a statement-planting contract
that fixes the exact tail-decay producer whose bound the compact support plus
trace split demands.  The genuinely missing analytic estimate is the tail
operator-norm / tail-trace decay of `R^(> B)`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawRenewalTailBound

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkovRawRenewalBridge
open CCM24FiniteSCausalMarkovRawRenewalSupportSplit
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The real ordinary trace of the complete physical renewal owner splits
exactly into the compact-displacement real trace plus the tail real trace, on
any source basis along which both pieces are trace class.  This is the
operator-level Proof 807 split read back onto the trace, before any absolute
value is taken. -/
theorem inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail
    {rho : Type*} (B : ℝ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hsupport : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family))
    (htail : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)) :
    (ordinaryTraceAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family)).re =
      (ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re +
        (ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re := by
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail]
  rw [ordinaryTraceAlong_add sourceBasis
    (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)
    (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)
    hsupport htail]
  norm_num

/-- Bounding the compact real trace and the tail real trace separately is
sufficient for the raw Gate endpoint: the absolute real trace is bounded by the
sum of the two piece bounds.  This is the exact triangle/assembly step that a
tail decay producer consumes. -/
theorem inverseLowerFactorPhysicalRenewalTrace_split_bound
    {rho : Type*} (B : ℝ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (boundSupport boundTail : ℝ)
    (hsupport : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family))
    (htail : IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family))
    (hboundSupport : |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re| ≤
        boundSupport)
    (hboundTail : |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re| ≤
        boundTail) :
    |(ordinaryTraceAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family)).re| ≤
        boundSupport + boundTail := by
  rw [inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail B owner lambda
    family sourceBasis hsupport htail]
  calc
    |((ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re +
        (ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re)| ≤
        |(ordinaryTraceAlong sourceBasis
            (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re| +
          |(ordinaryTraceAlong sourceBasis
            (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re| :=
      abs_add_le _ _
    _ ≤ boundSupport + boundTail := add_le_add hboundSupport hboundTail

/-- A producer for a tail trace-decay bound, uniform in the visible finite
family, closes the canonical real Gate exactly: the compact part is discarded
in favor of a single uniform tail bound applied to the whole Gate object with
compact root support before any absolute value.  This is the `(AA.32)` handoff
consumed through the already declared lower-factor persistence closure. -/
theorem canonicalRealGate3UAt_of_tailNormBound
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (bound : ℝ)
    (hdecay :
      |(ordinaryTraceAlong sourceBasis
        (inverseLowerFactorPhysicalRenewalResponse owner lambda
          (canonicalFamily owner))).re| ≤ bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound := by
  rw [canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le
    owner lambda sourceBasis bound]
  exact hdecay

end CCM24FiniteSCausalMarkovRawRenewalTailBound
end CCM25Concrete
end Source
end ConnesWeilRH