/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnFullCarrierPairReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerCompression

/-!
# Adjoint support ledger for the radial boundary channel

Proof 689 closes the reverse carrier identities for the bare radial boundary
channel.  The forward channel has no upper-radial output and is absorbed by
the suffix Sonin range projection.  After taking the adjoint, the order is
reversed: the adjoint kills upper-radial input and is fixed by the suffix
range projection on the left.

These are exact carrier identities.  They do not turn the bounded radial
crossing into a Hilbert--Schmidt pair and do not provide Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryAdjointSupport

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwnerCompression
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierPairReadout
open AntiresonantFrameLossRadialBoundaryColumnPairAlignment
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open AntiresonantFrameLossCommutator
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Basis-free adjoint identities -/

/-- The adjoint of the positive radial boundary crossing is the reverse
translation followed by the complementary radial projection, with the
suffix range projection on the left. -/
theorem radialSoninBoundaryCrossing_adjoint_eq_reverse
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (radialSoninBoundaryCrossing p S)† =
      newSuffixRangeProjection unitSoninScale S ∘L
        (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap ∘L
        radialComplement unitSoninScale := by
  have hprojection :
      (newSuffixRangeProjection unitSoninScale S)† =
        newSuffixRangeProjection unitSoninScale S := by
    rw [newSuffixRangeProjection_eq_semilocalSoninStarProjection]
    exact isStarProjection_starProjection.isSelfAdjoint.adjoint_eq
  have htranslation :
      ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap)† =
        (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap := by
    simpa only [neg_neg] using
      (SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint
        (-Real.log p))
  have hcomplement :
      (radialComplement unitSoninScale)† =
        radialComplement unitSoninScale := by
    exact (radialSupportProjection_isStarProjection unitSoninScale).one_sub
      |>.isSelfAdjoint.adjoint_eq
  rw [radialSoninBoundaryCrossing,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hprojection, htranslation, hcomplement]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The adjoint boundary channel annihilates upper-radial input. -/
theorem radialSoninBoundaryCrossing_adjoint_comp_radialSupport_eq_zero
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (radialSoninBoundaryCrossing p S)† ∘L
        radialSupportProjection unitSoninScale = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialSupportProjection_comp_radialSoninBoundaryCrossing_eq_zero p S)
  have hprojection :
      (radialSupportProjection unitSoninScale)† =
        radialSupportProjection unitSoninScale := by
    exact (radialSupportProjection_isStarProjection unitSoninScale).isSelfAdjoint.adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, hprojection, map_zero] using h

/-- The adjoint boundary channel is fixed by the suffix range projection on
the left. -/
theorem newSuffixRangeProjection_comp_radialSoninBoundaryCrossing_adjoint_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection unitSoninScale S ∘L
        (radialSoninBoundaryCrossing p S)† =
      (radialSoninBoundaryCrossing p S)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self p S)
  have hprojection :
      (newSuffixRangeProjection unitSoninScale S)† =
        newSuffixRangeProjection unitSoninScale S := by
    rw [newSuffixRangeProjection_eq_semilocalSoninStarProjection]
    exact isStarProjection_starProjection.isSelfAdjoint.adjoint_eq
  simpa only [ContinuousLinearMap.adjoint_comp, hprojection] using h

/-! ## Transfer to the conditional pair owner -/

/-- The boundary pair's forward trace product has no upper-radial output. -/
theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_comp_radialSupport_eq_zero
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    radialSupportProjection unitSoninScale ∘L
        data.ownerData.boundaryData.traceProduct = 0 := by
  rw [data.ownerData.boundary_traceProduct_eq]
  exact radialSupportProjection_comp_radialSoninBoundaryCrossing_eq_zero
    p family.visiblePrimes

/-- Swapping the boundary pair exposes the exact adjoint input support. -/
theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_swap_comp_radialSupport_eq_zero
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    data.ownerData.boundaryData.swap.traceProduct ∘L
        radialSupportProjection unitSoninScale = 0 := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
    data.ownerData.boundary_traceProduct_eq]
  exact radialSoninBoundaryCrossing_adjoint_comp_radialSupport_eq_zero
    p family.visiblePrimes

/-- Swapping the boundary pair preserves the suffix range on the left. -/
theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.newSuffixRangeProjection_comp_boundaryTraceProduct_swap_eq_self
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    newSuffixRangeProjection unitSoninScale family.visiblePrimes ∘L
        data.ownerData.boundaryData.swap.traceProduct =
      data.ownerData.boundaryData.swap.traceProduct := by
  rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
    data.ownerData.boundary_traceProduct_eq]
  exact newSuffixRangeProjection_comp_radialSoninBoundaryCrossing_adjoint_eq_self
    p family.visiblePrimes

end AntiresonantFrameLossRadialBoundaryAdjointSupport
end CCM25Concrete
end Source
end ConnesWeilRH
