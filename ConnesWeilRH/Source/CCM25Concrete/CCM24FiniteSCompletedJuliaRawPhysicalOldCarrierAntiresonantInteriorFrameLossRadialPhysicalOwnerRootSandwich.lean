/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerTwoCarrierSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# Same-domain root sandwich for the signed radial owner

Proof 680 attaches the existing common-root Hilbert--Schmidt interface to the
signed radial owner from Proof 679.  The owner is kept on its original
`finiteSCarrier`; the two carrier readout is used only as an exact algebraic
normal form.  The resulting trace and compactness statements are legality
results, not a Gate 3U estimate or a sign theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerRootSandwich

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCommonBoundaryPair
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialInteriorPhysicalExpansion
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerTwoCarrierSplit
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Root-sandwich producer -/

/-- A common-root owner for a bounded same-domain sandwich of the signed
radial physical owner.  The response field is deliberately tied to the
complete owner rather than to either carrier compression. -/
structure RadialSignedOwnerRootS2Producer
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ finiteSCarrier) where
  p : CCM24VisiblePrime
  S : List CCM24VisiblePrime
  base : CommonRootS2Producer (K := K) (G := G) sourceBasis
  leftSandwich : finiteSCarrier →L[ℂ] finiteSCarrier
  rightSandwich : finiteSCarrier →L[ℂ] finiteSCarrier
  response_eq_owner :
    base.response =
      leftSandwich ∘L radialSignedPhysicalOwner p S ∘L rightSandwich

/-! ## Exact two-carrier readback -/

/-- The root response reads back to the two-carrier normal form from Proof
679.  The upper three-branch and lower boundary terms remain summed only after
the common same-domain sandwich is applied. -/
theorem RadialSignedOwnerRootS2Producer.response_eq_twoCarrierNormalForm
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis) :
    producer.base.response =
      producer.leftSandwich ∘L
          (radialSupportProjection unitSoninScale ∘L
            (-cc20ThreeBranchCommutator
              (radialSupportProjection unitSoninScale)
              (parameterizedFourierSupportProjection unitSoninScale 1 producer.S
                (by norm_num))
              (parameterizedProlateRemainder unitSoninScale 1 producer.S
                (by norm_num))
              (radialCompressedPositiveTranslation producer.p))) ∘L
            producer.rightSandwich +
        producer.leftSandwich ∘L radialSoninBoundaryCrossing producer.p
          producer.S ∘L producer.rightSandwich := by
  rw [producer.response_eq_owner,
    radialSignedPhysicalOwner_eq_upperThreeBranch_add_boundary]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add]

/-! ## Trace-class and compact readout -/

/-- The complete same-domain owner is trace class along the named source
basis whenever its common-root producer is available. -/
theorem RadialSignedOwnerRootS2Producer.isTraceClassAlong
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis) :
    PositiveTrace.IsTraceClassAlong sourceBasis producer.base.response := by
  rw [← CCM24FiniteSCommonBoundaryPair.commonRootS2PairData_traceProduct_eq_response
    producer.base]
  exact CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct_isTraceClassAlong
    (CCM24FiniteSCommonBoundaryPair.commonRootS2PairData producer.base)

/-- The same trace-class witness applies to the actual signed radial owner
after the bounded left/right sandwich. -/
theorem RadialSignedOwnerRootS2Producer.sandwichedOwner_isTraceClassAlong
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      (producer.leftSandwich ∘L radialSignedPhysicalOwner producer.p producer.S
        ∘L producer.rightSandwich) := by
  rw [← producer.response_eq_owner]
  exact producer.isTraceClassAlong

/-- With a target Hilbert basis, the same root owner is a genuine compact
operator. -/
theorem RadialSignedOwnerRootS2Producer.sandwichedOwner_isCompactOperator
    {ι κ K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis)
    (targetBasis : HilbertBasis κ ℂ G) :
    IsCompactOperator
      (producer.leftSandwich ∘L radialSignedPhysicalOwner producer.p producer.S
        ∘L producer.rightSandwich) := by
  rw [← producer.response_eq_owner,
    ← CCM24FiniteSCommonBoundaryPair.commonRootS2PairData_traceProduct_eq_response
      producer.base]
  exact CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct_isCompactOperator
    targetBasis
    (CCM24FiniteSCommonBoundaryPair.commonRootS2PairData producer.base)

/-! ## Ordinary trace bound -/

/-- The generic common-root trace bound can be read directly on the complete
signed owner, with no branchwise absolute-value split. -/
theorem RadialSignedOwnerRootS2Producer.sandwichedOwner_ordinaryTrace_norm_le
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis) :
    ‖PositiveTrace.ordinaryTraceAlong sourceBasis
      (producer.leftSandwich ∘L radialSignedPhysicalOwner producer.p producer.S
        ∘L producer.rightSandwich)‖ ≤
      (1 / 2 : ℝ) * (‖producer.base.leftFactor‖ ^ 2 + 1) *
        (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) := by
  rw [← producer.response_eq_owner]
  exact CCM24FiniteSCommonBoundaryPair.commonRootS2Producer_ordinaryTrace_norm_le
    producer.base

/-- A route-uniform root-energy and left-factor bound passes through the
complete signed owner without separating its two carrier channels. -/
theorem RadialSignedOwnerRootS2Producer.sandwichedOwner_ordinaryTrace_norm_le_of_bounds
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis)
    (rootBound leftFactorBound : ℝ)
    (hroot : (∑' i, ‖producer.base.root (sourceBasis i)‖ ^ 2) ≤ rootBound)
    (hroot_nonneg : 0 ≤ rootBound)
    (hleft : ‖producer.base.leftFactor‖ ≤ leftFactorBound)
    (hleft_nonneg : 0 ≤ leftFactorBound) :
    ‖PositiveTrace.ordinaryTraceAlong sourceBasis
      (producer.leftSandwich ∘L radialSignedPhysicalOwner producer.p producer.S
        ∘L producer.rightSandwich)‖ ≤
      (1 / 2 : ℝ) * (leftFactorBound ^ 2 + 1) * rootBound := by
  rw [← producer.response_eq_owner]
  exact CCM24FiniteSCommonBoundaryPair.commonRootS2Producer_ordinaryTrace_norm_le_of_bounds
    producer.base rootBound leftFactorBound hroot hroot_nonneg hleft hleft_nonneg

end AntiresonantFrameLossRadialPhysicalOwnerRootSandwich
end CCM25Concrete
end Source
end ConnesWeilRH
