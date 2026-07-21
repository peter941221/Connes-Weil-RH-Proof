/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointBoundaryCollapse

/-!
# Rectangular prefix defects as complementary tails

A rectangular prefix matrix does not preserve products because the intermediate
Hilbert carrier is truncated.  This module constructs the finite-rank basis
projection explicitly and identifies each product defect with a compression of
the genuine complementary-tail operator `A (I - P_N) B`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRectangularTailFactorization

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSRectangularPrefixCycle
open CCM24FiniteSEndpointBoundaryCollapse
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSCanonicalCompletedResponse

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Finite-rank projection onto the first `N` vectors of a natural Hilbert
basis. -/
noncomputable def basisPrefixProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) : H →L[ℂ] H :=
  ∑ k : Fin N,
    InnerProductSpace.rankOne ℂ (basis (k : ℕ)) (basis (k : ℕ))

theorem basisPrefixProjection_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ) (x : H) :
    basisPrefixProjection basis N x =
      ∑ k : Fin N, ⟪basis (k : ℕ), x⟫_ℂ • basis (k : ℕ) := by
  simp [basisPrefixProjection, InnerProductSpace.rankOne_apply]

/-- Multiplying rectangular prefix matrices inserts the finite-rank prefix
projection on their intermediate source carrier. -/
theorem rectangularPrefixMatrix_mul_eq_targetCompression_prefixProjection
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward *
        rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse =
      basisPrefixMatrix targetBasis targetN
        (forward ∘L basisPrefixProjection sourceBasis sourceN ∘L reverse) := by
  ext i j
  unfold rectangularPrefixMatrix basisPrefixMatrix
  rw [Matrix.mul_apply]
  simp only [ContinuousLinearMap.comp_apply,
    basisPrefixProjection_apply, map_sum, map_smul, inner_sum,
    inner_smul_right]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The reversed rectangular product inserts the target prefix projection. -/
theorem rectangularPrefixMatrix_mul_eq_sourceCompression_prefixProjection
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse *
        rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward =
      basisPrefixMatrix sourceBasis sourceN
        (reverse ∘L basisPrefixProjection targetBasis targetN ∘L forward) := by
  exact rectangularPrefixMatrix_mul_eq_targetCompression_prefixProjection
    targetBasis sourceBasis targetN sourceN reverse forward

/-- The target product defect is exactly the target compression of the source
prefix-complement tail. -/
theorem rectangularTargetProductDefect_eq_tailCompression
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularTargetProductDefect sourceBasis targetBasis sourceN targetN
        forward reverse =
      basisPrefixMatrix targetBasis targetN
        (forward ∘L (1 - basisPrefixProjection sourceBasis sourceN) ∘L
          reverse) := by
  rw [rectangularTargetProductDefect,
    rectangularPrefixMatrix_mul_eq_targetCompression_prefixProjection]
  ext i j
  simp [basisPrefixMatrix, ContinuousLinearMap.comp_apply, inner_sub_right]

/-- The source product defect is exactly the source compression of the target
prefix-complement tail. -/
theorem rectangularSourceProductDefect_eq_tailCompression
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularSourceProductDefect sourceBasis targetBasis sourceN targetN
        forward reverse =
      basisPrefixMatrix sourceBasis sourceN
        (reverse ∘L (1 - basisPrefixProjection targetBasis targetN) ∘L
          forward) := by
  rw [rectangularSourceProductDefect,
    rectangularPrefixMatrix_mul_eq_sourceCompression_prefixProjection]
  ext i j
  simp [basisPrefixMatrix, ContinuousLinearMap.comp_apply, inner_sub_right]

/-- The scalar rectangular cycle boundary is the difference of its source and
target complementary-tail compressions. -/
noncomputable def rectangularPrefixTailBoundaryTrace
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) : ℂ :=
  Matrix.trace (basisPrefixMatrix targetBasis targetN
      (forward ∘L (1 - basisPrefixProjection sourceBasis sourceN) ∘L
        reverse)) -
    Matrix.trace (basisPrefixMatrix sourceBasis sourceN
      (reverse ∘L (1 - basisPrefixProjection targetBasis targetN) ∘L
        forward))

theorem rectangularPrefixCycleBoundaryTrace_eq_tailBoundaryTrace
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularPrefixCycleBoundaryTrace sourceBasis targetBasis sourceN
        targetN forward reverse =
      rectangularPrefixTailBoundaryTrace sourceBasis targetBasis sourceN
        targetN forward reverse := by
  unfold rectangularPrefixCycleBoundaryTrace
    rectangularPrefixTailBoundaryTrace
  rw [rectangularTargetProductDefect_eq_tailCompression,
    rectangularSourceProductDefect_eq_tailCompression]

/-- The endpoint boundary from Proof 458 written entirely as complementary
prefix tails. -/
noncomputable def actualBandEndpointTailBoundaryTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : ℂ :=
  rectangularPrefixTailBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandBaseRootLeg owner lambda).adjoint -
    rectangularPrefixTailBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandTargetDualRootLeg owner lambda family)
      (actualBandTargetFrameRootLeg owner lambda family).adjoint

theorem actualBandEndpointRectangularBoundaryTrace_eq_tailBoundaryTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointRectangularBoundaryTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      actualBandEndpointTailBoundaryTrace globalBasis lambda sourceBasis
        globalN sourceN owner family := by
  unfold actualBandEndpointRectangularBoundaryTrace
    actualBandEndpointTailBoundaryTrace
  rw [rectangularPrefixCycleBoundaryTrace_eq_tailBoundaryTrace,
    rectangularPrefixCycleBoundaryTrace_eq_tailBoundaryTrace]

/-- The active endpoint owner is the source Gram prefix plus the complete
tail-boundary difference. -/
theorem sourceGram_add_tailBoundary_eq_two_integral_weightedBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
        (sourceBandGramResponse owner lambda family))).re +
        (actualBandEndpointTailBoundaryTrace globalBasis lambda sourceBasis
          globalN sourceN owner family).re =
      2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha family.visiblePrimes := by
  rw [← actualBandEndpointRectangularBoundaryTrace_eq_tailBoundaryTrace]
  exact sourceGram_add_boundary_eq_two_integral_weightedBoundary globalBasis
    lambda sourceBasis globalN sourceN owner family

/-- Canonical consumer for the source Gram prefix plus its explicit pair of
complementary-tail boundary cycles. -/
theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_sourceGramTailBound
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (sourceCutoff : ℕ → ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (htrace : PositiveTrace.IsTraceClassAlong globalBasis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ globalN : ℕ,
      |(Matrix.trace (basisPrefixMatrix sourceBasis (sourceCutoff globalN)
          (sourceBandGramResponse owner lambda (canonicalFamily owner)))).re +
        (actualBandEndpointTailBoundaryTrace globalBasis lambda sourceBasis
          globalN (sourceCutoff globalN) owner (canonicalFamily owner)).re| ≤
        2 * ((owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3))) :
    ‖PositiveTrace.ordinaryTraceAlong globalBasis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  apply
    canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_sourceGramBoundaryBound
      globalBasis lambda sourceBasis sourceCutoff owner htrace
  intro globalN
  rw [actualBandEndpointRectangularBoundaryTrace_eq_tailBoundaryTrace]
  exact hbound globalN

end CCM24FiniteSRectangularTailFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
