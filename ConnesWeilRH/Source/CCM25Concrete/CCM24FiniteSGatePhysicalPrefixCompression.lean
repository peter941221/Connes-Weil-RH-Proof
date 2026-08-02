/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalFiniteDiagonalLimit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandPrefixCompression

/-!
# Ordered prefix compression for the physical Gate response

Proof 734 accepts a bound for every finite subset of an arbitrary Hilbert
basis.  Such an all-finsets hypothesis permits positive/negative subset
selection and can be much stronger than the signed Gate estimate.  This file
uses one natural Hilbert basis and only its nested `Finset.range N` exhaustion.

Each prefix is owned by the ordinary trace of the literal `Fin N` compression
matrix.  Fixed-family trace legality then passes the prefix bound to the
ordinary Gate trace.  No infinite trace cycle or branchwise trace norm is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixCompression

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace Matrix

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalFiniteDiagonalLimit
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The literal `Fin N` compression trace of the complete physical Gate
response in one natural Hilbert basis. -/
noncomputable def sourceGatePhysicalPrefixCompressionTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  Matrix.trace (basisPrefixMatrix basis N
    (lowerFactorGaugedActualBandCompletedRelativeResponse
      owner lambda family))

/-- The finite compression trace is exactly the ordered prefix of Proof 733's
complete signed scalar. -/
theorem sourceGatePhysicalPrefixCompressionTrace_eq_rangeSignedDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceGatePhysicalPrefixCompressionTrace owner lambda family basis N =
      ∑ i ∈ Finset.range N, sourceGatePhysicalSignedDiagonalScalar
        owner lambda family (basis i) := by
  rw [sourceGatePhysicalPrefixCompressionTrace,
    trace_basisPrefixMatrix_eq_rangeDiagonal]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_lowerFactorGaugedResponse_eq_signedDiagonalScalar
    owner lambda family (basis i)

private theorem norm_tsum_le_of_forall_range_norm_sum_le
    (f : ℕ → ℂ) (hf : Summable f) (bound : ℝ)
    (hbound : ∀ N : ℕ, ‖∑ i ∈ Finset.range N, f i‖ ≤ bound) :
    ‖∑' i, f i‖ ≤ bound := by
  exact le_of_tendsto'
    (continuous_norm.continuousAt.tendsto.comp
      hf.hasSum.tendsto_sum_nat) hbound

/-- A bound along one ordered natural-basis exhaustion passes to the ordinary
Gate trace.  Unlike Proof 734, no arbitrary finite-subset bound is required. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_rangeSignedDiagonalBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda)) (bound : ℝ)
    (htrace : IsTraceClassAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖∑ i ∈ Finset.range N, sourceGatePhysicalSignedDiagonalScalar
        owner lambda family (basis i)‖ ≤ bound) :
    ‖ordinaryTraceAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  rw [IsTraceClassAlong] at htrace
  rw [ordinaryTraceAlong]
  apply norm_tsum_le_of_forall_range_norm_sum_le _ htrace bound
  intro N
  have hfinite :
      (∑ i ∈ Finset.range N,
        ⟪basis i, lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family (basis i)⟫_ℂ) =
        ∑ i ∈ Finset.range N, sourceGatePhysicalSignedDiagonalScalar
          owner lambda family (basis i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact inner_lowerFactorGaugedResponse_eq_signedDiagonalScalar
      owner lambda family (basis i)
  rw [hfinite]
  exact hbound N

/-- The same ordered-exhaustion consumer stated directly on the finite
compression matrices that expose the finite-dimensional analytic target. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixCompressionBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda)) (bound : ℝ)
    (htrace : IsTraceClassAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixCompressionTrace
        owner lambda family basis N‖ ≤ bound) :
    ‖ordinaryTraceAlong basis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_rangeSignedDiagonalBound
    owner lambda family basis bound htrace
  intro N
  rw [← sourceGatePhysicalPrefixCompressionTrace_eq_rangeSignedDiagonal]
  exact hbound N

/-- The existing fixed-family Hilbert--Schmidt owner supplies trace legality;
the only new premise is the ordered finite-compression bound. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixCompressionBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ : Type*}
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
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixCompressionTrace
        owner lambda family sourceBasis N‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_prefixCompressionBound
    owner lambda family sourceBasis bound
  · exact lowerFactorGaugedActualBandCompletedRelativeResponse_isTraceClassAlong
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  · exact hbound

end CCM24FiniteSGatePhysicalPrefixCompression
end CCM25Concrete
end Source
end ConnesWeilRH
