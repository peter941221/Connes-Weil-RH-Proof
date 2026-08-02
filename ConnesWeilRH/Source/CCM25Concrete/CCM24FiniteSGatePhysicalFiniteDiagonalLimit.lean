/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalSignedDiagonal

/-!
# Finite-diagonal limit for the physical Gate response

Proof 733 identifies every diagonal coefficient of the Gate response while
keeping the forward and physical-leakage crossings in one signed scalar.  This
file supplies the corresponding trace-limit principle: a common bound for all
finite sums of those complete scalars passes to the ordinary trace.

The full Gate diagonal is already summable by the fixed-family Hilbert--Schmidt
owner.  No separate summability of the displayed forward and leakage pieces is
assumed or concluded.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalFiniteDiagonalLimit

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete signed scalar from Proof 733.  The two coordinates remain
inside one complex number. -/
noncomputable def sourceGatePhysicalSignedDiagonalScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) : ℂ :=
  ((2 * (⟪sourceInclusion lambda x,
    detectorOperator owner
      (sourceActualBandForwardCoframe lambda family x)⟫_ℂ).re : ℝ) : ℂ) +
  ⟪sourceInclusion lambda x,
    detectorOperator owner
      (sourcePhysicalCoframeLeakage lambda family x)⟫_ℂ

/-- The named scalar is exactly the literal Gate diagonal coefficient. -/
theorem inner_lowerFactorGaugedResponse_eq_signedDiagonalScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    ⟪x, lowerFactorGaugedActualBandCompletedRelativeResponse
      owner lambda family x⟫_ℂ =
      sourceGatePhysicalSignedDiagonalScalar owner lambda family x := by
  exact inner_lowerFactorGaugedResponse_eq_two_re_add_physicalLeakage
    owner lambda family x

private theorem norm_tsum_le_of_forall_finset_norm_sum_le
    {ι : Type*} (f : ι → ℂ) (hf : Summable f) (bound : ℝ)
    (hbound : ∀ terms : Finset ι, ‖∑ i ∈ terms, f i‖ ≤ bound) :
    ‖∑' i, f i‖ ≤ bound := by
  exact le_of_tendsto'
    (continuous_norm.continuousAt.tendsto.comp hf.hasSum) hbound

/-- A uniform bound for every finite sum of the complete signed diagonal
passes to the ordinary Gate trace. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_finiteSignedDiagonalBound
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) (bound : ℝ)
    (htrace : IsTraceClassAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (hbound : ∀ terms : Finset ι,
      ‖∑ i ∈ terms, sourceGatePhysicalSignedDiagonalScalar
        owner lambda family (basis i)‖ ≤ bound) :
    ‖ordinaryTraceAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  rw [IsTraceClassAlong] at htrace
  rw [ordinaryTraceAlong]
  apply norm_tsum_le_of_forall_finset_norm_sum_le _ htrace bound
  intro terms
  have hfinite :
      (∑ i ∈ terms,
        ⟪basis i, lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family (basis i)⟫_ℂ) =
        ∑ i ∈ terms, sourceGatePhysicalSignedDiagonalScalar
          owner lambda family (basis i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact inner_lowerFactorGaugedResponse_eq_signedDiagonalScalar
      owner lambda family (basis i)
  rw [hfinite]
  exact hbound terms

/-- The source-specific Hilbert--Schmidt owner supplies trace legality, so the
only remaining premise is the complete finite signed-diagonal bound. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_pairData_finiteSignedDiagonalBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound : ∀ terms : Finset ρ,
      ‖∑ i ∈ terms, sourceGatePhysicalSignedDiagonalScalar
        owner lambda family (sourceBasis i)‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_finiteSignedDiagonalBound
    owner lambda family sourceBasis bound
  · exact lowerFactorGaugedActualBandCompletedRelativeResponse_isTraceClassAlong
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  · exact hbound

end CCM24FiniteSGatePhysicalFiniteDiagonalLimit
end CCM25Concrete
end Source
end ConnesWeilRH
