/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerCommonRootPairData

/-!
# Trace consumer for the signed radial pair-data owner

Proof 684 consumes the exact pair-data contract from Proof 683.  Once the two
physical pair products are supplied, their orthogonal signed packing gives
named-basis trace-class legality and compactness for the complete radial owner.
The same result is then read through the bounded root sandwich.

These are conditional Gate 3L/readout results.  They do not bound the pair
energies uniformly in the finite-S family and therefore do not close Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairDataTraceConsumer

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
open AntiresonantFrameLossRadialPhysicalOwnerRootSandwich
open CCM24FiniteSProjectionTrace

/-- The complete signed radial owner is trace class along the named source
basis whenever the two physical pair owners from Proof 683 are supplied. -/
theorem RadialSignedPhysicalOwnerPairData.isTraceClassAlong
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    IsTraceClassAlong sourceBasis
      (radialSignedPhysicalOwner p family.visiblePrimes) := by
  rw [← data.signedPairData_traceProduct_eq_owner]
  exact data.signedPairData.traceProduct_isTraceClassAlong

/-- With a target basis for the packed pair carrier, the complete signed radial
owner is a genuine compact operator. -/
theorem RadialSignedPhysicalOwnerPairData.isCompactOperator
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι κ K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis)
    (targetBasis : HilbertBasis κ ℂ (WithLp 2 (K × G))) :
    IsCompactOperator
      (radialSignedPhysicalOwner p family.visiblePrimes) := by
  rw [← data.signedPairData_traceProduct_eq_owner]
  exact data.signedPairData.traceProduct_isCompactOperator targetBasis

/-- The root producer from Proof 683 carries the same trace-class legality
through its bounded same-domain sandwich without splitting the signed owner. -/
theorem RadialSignedOwnerRootS2Producer.sandwichedOwner_isTraceClassAlong_of_pairData
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι κ K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis)
    (targetBasis : HilbertBasis κ ℂ (WithLp 2 (K × G)))
    (leftSandwich rightSandwich : finiteSCarrier →L[ℂ] finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      ((radialSignedOwnerRootS2ProducerOfPairData data targetBasis
        leftSandwich rightSandwich).leftSandwich ∘L
        radialSignedPhysicalOwner p family.visiblePrimes ∘L
        (radialSignedOwnerRootS2ProducerOfPairData data targetBasis
          leftSandwich rightSandwich).rightSandwich) := by
  exact RadialSignedOwnerRootS2Producer.sandwichedOwner_isTraceClassAlong
    (radialSignedOwnerRootS2ProducerOfPairData data targetBasis
      leftSandwich rightSandwich)

end AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairDataTraceConsumer
end CCM25Concrete
end Source
end ConnesWeilRH
