/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwich
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment

/-!
# Root-sandwich endpoint alignment for the signed radial owner

Proof 682 rewrites the root-sandwich response from the parameterized endpoint
objects to the target projections selected by the same finite prime-power
family.  The suffix equality is an explicit hypothesis: a producer for an
unrelated list cannot be silently reused for the finite-S target.

This is a carrier/readback theorem.  It does not construct the common root,
prove a boundary factorization, or close Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerRootSandwichFiniteSEndpointAlignment

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerRootSandwich
open AntiresonantFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-- At a finite-S endpoint, an aligned root-sandwich response uses the actual
target Fourier/prolate projections, while the signed boundary channel remains
inside the same sandwich. -/
theorem RadialSignedOwnerRootS2Producer.response_eq_targetThreeBranch_add_boundary
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (producer : RadialSignedOwnerRootS2Producer (K := K) (G := G)
      sourceBasis)
    (family : FinitePrimePowerFamily)
    (hS : producer.S = family.visiblePrimes) :
    producer.base.response =
      producer.leftSandwich ∘L
          (-cc20ThreeBranchCommutator
            (radialSupportProjection unitSoninScale)
            (targetFourierSupportProjection unitSoninScale family)
            (targetProlateRemainder unitSoninScale family)
            (radialCompressedPositiveTranslation producer.p)) ∘L
            producer.rightSandwich +
        producer.leftSandwich ∘L
          radialSoninBoundaryCrossing producer.p family.visiblePrimes ∘L
            producer.rightSandwich := by
  rw [producer.response_eq_owner, hS,
    radialSignedPhysicalOwner_one_eq_targetThreeBranch_add_boundary]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add]

end AntiresonantFrameLossRadialPhysicalOwnerRootSandwichFiniteSEndpointAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
