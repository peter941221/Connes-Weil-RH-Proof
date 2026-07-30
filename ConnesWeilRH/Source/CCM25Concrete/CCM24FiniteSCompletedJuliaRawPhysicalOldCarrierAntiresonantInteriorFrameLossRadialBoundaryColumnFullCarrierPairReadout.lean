/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnFullCarrierExtension

/-!
# Align the full-carrier boundary pair with its column readout

Proof 688 consumes the full-carrier extension from Proof 687 and the explicit
pair contract from Proof 686.  It identifies the boundary pair's trace
product with the extended channel, proves that the pair absorbs the actual
polar range projection, and transfers the relative `32 * bound` estimate to
every ambient input.

The result is still conditional on the full-carrier Hilbert--Schmidt pair in
`ownerData.boundaryData`; it does not construct that pair or close Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryColumnFullCarrierPairReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open AntiresonantFrameLossRadialBoundaryColumnPairAlignment
open AntiresonantFrameLossRadialBoundarySplit
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_eq_fullCarrierReadout
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    data.ownerData.boundaryData.traceProduct =
      fullCarrierBoundaryChannelReadout data.boundaryColumnData := by
  rw [data.ownerData.boundary_traceProduct_eq,
    fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing]

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_comp_newSuffixRangeProjection_eq_self
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    data.ownerData.boundaryData.traceProduct ∘L
        newSuffixRangeProjection unitSoninScale family.visiblePrimes =
      data.ownerData.boundaryData.traceProduct := by
  calc
    data.ownerData.boundaryData.traceProduct ∘L
          newSuffixRangeProjection unitSoninScale family.visiblePrimes =
        fullCarrierBoundaryChannelReadout data.boundaryColumnData ∘L
          newSuffixRangeProjection unitSoninScale family.visiblePrimes := by
      rw [RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_eq_fullCarrierReadout
        data]
    _ = radialSoninBoundaryCrossing p family.visiblePrimes ∘L
          newSuffixRangeProjection unitSoninScale family.visiblePrimes := by
      rw [fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing]
    _ = radialSoninBoundaryCrossing p family.visiblePrimes :=
      radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self
        p family.visiblePrimes
    _ = data.ownerData.boundaryData.traceProduct := by
      rw [← data.ownerData.boundary_traceProduct_eq]

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_apply_norm_le_fullCarrierColumn
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound)
    (u : finiteSCarrier) :
    ‖data.ownerData.boundaryData.traceProduct u‖ ≤
      (32 * bound) *
        ‖newFrameAntiresonantColumn unitSoninScale p family.visiblePrimes
          (ContinuousLinearMap.adjoint
            (newSuffixFrame unitSoninScale family.visiblePrimes) u)‖ := by
  rw [RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_eq_fullCarrierReadout
    data]
  exact norm_fullCarrierBoundaryChannelReadout_apply_le
    data.boundaryColumnData u

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_apply_normSq_le_fullCarrierColumn
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound)
    (u : finiteSCarrier) :
    ‖data.ownerData.boundaryData.traceProduct u‖ ^ 2 ≤
      (32 * bound) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p family.visiblePrimes
          (ContinuousLinearMap.adjoint
            (newSuffixFrame unitSoninScale family.visiblePrimes) u)‖ ^ 2 := by
  have hnorm :=
    RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_apply_norm_le_fullCarrierColumn
      data u
  have hbound : 0 ≤ 32 * bound :=
    mul_nonneg (by norm_num) data.boundaryColumnData.bound_nonneg
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound (norm_nonneg _))).2 hnorm

end AntiresonantFrameLossRadialBoundaryColumnFullCarrierPairReadout
end CCM25Concrete
end Source
end ConnesWeilRH
