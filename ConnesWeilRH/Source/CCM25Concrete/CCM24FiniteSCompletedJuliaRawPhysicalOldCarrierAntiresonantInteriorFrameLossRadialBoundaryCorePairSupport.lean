/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryAdjointSupport

/-!
# Core pair support ledger for the radial boundary channel

Proof 690 removes the finite-column contract from the exact support identities
of the conditional radial boundary pair.  The producer still has to supply
the full-carrier `BasisHilbertSchmidtPairData`; this module only says what any
such producer must satisfy after its trace-product readback is installed.

In particular, the forward product is killed by the upper-radial projection,
the swapped product is killed on upper-radial input, and the two products keep
the expected suffix Sonin range projection.  No Hilbert--Schmidt producer or
finite-S-uniform estimate is inferred.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryCorePairSupport

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwnerCompression
open AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open AntiresonantFrameLossRadialBoundaryAdjointSupport

/-! ## Forward product -/

/-- Any full-carrier boundary pair has no upper-radial output. -/
theorem RadialSignedPhysicalOwnerPairData.boundaryTraceProduct_comp_radialSupport_eq_zero
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    radialSupportProjection unitSoninScale ∘L
        data.boundaryData.traceProduct = 0 := by
  rw [data.boundary_traceProduct_eq]
  exact radialSupportProjection_comp_radialSoninBoundaryCrossing_eq_zero
    p family.visiblePrimes

/-- The forward boundary product is fixed by the suffix Sonin range on the
right. -/
theorem RadialSignedPhysicalOwnerPairData.boundaryTraceProduct_comp_newSuffixRangeProjection_eq_self
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    data.boundaryData.traceProduct ∘L
        newSuffixRangeProjection unitSoninScale family.visiblePrimes =
      data.boundaryData.traceProduct := by
  rw [data.boundary_traceProduct_eq]
  exact radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self
    p family.visiblePrimes

/-! ## Swapped product -/

/-- The swapped boundary product has no upper-radial input. -/
theorem RadialSignedPhysicalOwnerPairData.boundaryTraceProduct_swap_comp_radialSupport_eq_zero
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    data.boundaryData.swap.traceProduct ∘L
        radialSupportProjection unitSoninScale = 0 := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
    data.boundary_traceProduct_eq]
  exact radialSoninBoundaryCrossing_adjoint_comp_radialSupport_eq_zero
    p family.visiblePrimes

/-- The swapped boundary product is fixed by the suffix Sonin range on the
left. -/
theorem RadialSignedPhysicalOwnerPairData.newSuffixRangeProjection_comp_boundaryTraceProduct_swap_eq_self
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    newSuffixRangeProjection unitSoninScale family.visiblePrimes ∘L
        data.boundaryData.swap.traceProduct =
      data.boundaryData.swap.traceProduct := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
    data.boundary_traceProduct_eq]
  exact newSuffixRangeProjection_comp_radialSoninBoundaryCrossing_adjoint_eq_self
    p family.visiblePrimes

end AntiresonantFrameLossRadialBoundaryCorePairSupport
end CCM25Concrete
end Source
end ConnesWeilRH
