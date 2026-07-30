/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerCommonRootPairData

/-!
# Align the radial column contract with the full boundary pair

Proof 686 keeps two obligations in one explicit structure:

* `ownerData.boundaryData` is a genuine full-carrier Hilbert--Schmidt pair
  whose trace product is the bare radial boundary channel;
* `boundaryColumnData` is a source-side finite-radial-column factorization.

The resulting theorems transfer the finite-column norm and kernel-visibility
consequences to the full pair only after restriction to the actual
`newSuffixFrame`.  No extension from that source carrier to all of
`finiteSCarrier` is inferred, and no route-uniform bound is claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryColumnPairAlignment

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundaryColumnBridge
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A full-carrier signed-owner pair together with the explicit source-side
finite-column contract for its radial boundary leg. -/
structure RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
    (p : CCM24VisiblePrime) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (N : ℕ) (bound : ℝ) where
  ownerData : RadialSignedPhysicalOwnerPairData
    (K := K) (G := G) p family sourceBasis
  boundaryColumnData :
    RadialBoundarySourceColumnFactorizationData
      p family.visiblePrimes N bound

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.signedPairData_traceProduct_eq_owner
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound) :
    data.ownerData.signedPairData.traceProduct =
      radialSignedPhysicalOwner p family.visiblePrimes := by
  exact data.ownerData.signedPairData_traceProduct_eq_owner

/-! ## Restricted norm transfer -/

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_comp_newSuffixFrame_norm_le
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖data.ownerData.boundaryData.traceProduct
        (newSuffixFrame unitSoninScale family.visiblePrimes x)‖ ≤
      (32 * bound) *
        ‖newFrameAntiresonantColumn unitSoninScale p
          family.visiblePrimes x‖ := by
  have htrace := DFunLike.congr_fun
    data.ownerData.boundary_traceProduct_eq
      (newSuffixFrame unitSoninScale family.visiblePrimes x)
  calc
    ‖data.ownerData.boundaryData.traceProduct
        (newSuffixFrame unitSoninScale family.visiblePrimes x)‖ =
        ‖radialSoninBoundaryCrossing p family.visiblePrimes
          (newSuffixFrame unitSoninScale family.visiblePrimes x)‖ := by
      rw [htrace]
    _ ≤ (32 * bound) *
          ‖newFrameAntiresonantColumn unitSoninScale p
            family.visiblePrimes x‖ :=
      norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
        data.boundaryColumnData x

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_comp_newSuffixFrame_normSq_le
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖data.ownerData.boundaryData.traceProduct
        (newSuffixFrame unitSoninScale family.visiblePrimes x)‖ ^ 2 ≤
      (32 * bound) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p
          family.visiblePrimes x‖ ^ 2 := by
  have hnorm :=
    data.boundaryTraceProduct_comp_newSuffixFrame_norm_le x
  have hbound : 0 ≤ 32 * bound :=
    mul_nonneg (by norm_num) data.boundaryColumnData.bound_nonneg
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound (norm_nonneg _))).2 hnorm

/-! ## Exact source-kernel visibility -/

theorem RadialSignedPhysicalOwnerPairDataWithBoundaryColumn.boundaryTraceProduct_eq_zero_of_boundaryColumn_eq_zero
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    {N : ℕ} {bound : ℝ}
    (data : RadialSignedPhysicalOwnerPairDataWithBoundaryColumn
      (K := K) (G := G) p family sourceBasis N bound)
    {x : sourceSoninCarrier unitSoninScale}
    (hx : finitePrimeEulerRadialGeometricBoundaryColumn
      unitSoninScale p family.visiblePrimes N x = 0) :
    data.ownerData.boundaryData.traceProduct
        (newSuffixFrame unitSoninScale family.visiblePrimes x) = 0 := by
  have hfactor := DFunLike.congr_fun
    data.boundaryColumnData.factorization x
  have hcross : radialSoninBoundaryCrossing p family.visiblePrimes
      (newSuffixFrame unitSoninScale family.visiblePrimes x) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using hfactor.symm
  have htrace := DFunLike.congr_fun
    data.ownerData.boundary_traceProduct_eq
      (newSuffixFrame unitSoninScale family.visiblePrimes x)
  rw [htrace, hcross]

end AntiresonantFrameLossRadialBoundaryColumnPairAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
