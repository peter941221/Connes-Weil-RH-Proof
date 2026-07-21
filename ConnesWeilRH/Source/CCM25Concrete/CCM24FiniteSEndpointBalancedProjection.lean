/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRectangularTailFactorization

/-!
# Balanced source/target prefix projection ledger

The source Gram endpoint and the complementary-tail boundary are not two
independent estimates.  Their base/base and dual/frame pieces combine exactly
into a source-side prefix projection and a target-side complementary projection.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointBalancedProjection

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSEndpointBoundaryCollapse
open CCM24FiniteSRectangularTailFactorization
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSCanonicalCompletedResponse

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source/target balanced form of the endpoint prefix ledger. -/
noncomputable def actualBandEndpointBalancedPrefixTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : ℝ :=
  (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
      ((actualBandBaseRootLeg owner lambda).adjoint ∘L
        basisPrefixProjection globalBasis globalN ∘L
          actualBandBaseRootLeg owner lambda -
        (actualBandTargetFrameRootLeg owner lambda family).adjoint ∘L
          basisPrefixProjection globalBasis globalN ∘L
            actualBandTargetDualRootLeg owner lambda family))).re +
    (Matrix.trace (basisPrefixMatrix globalBasis globalN
      (actualBandBaseRootLeg owner lambda ∘L
          (1 - basisPrefixProjection sourceBasis sourceN) ∘L
            (actualBandBaseRootLeg owner lambda).adjoint -
        actualBandTargetDualRootLeg owner lambda family ∘L
          (1 - basisPrefixProjection sourceBasis sourceN) ∘L
            (actualBandTargetFrameRootLeg owner lambda family).adjoint))).re

theorem actualBandEndpointBalancedPrefixTrace_eq_sourceGram_add_tailBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointBalancedPrefixTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (sourceBandGramResponse owner lambda family))).re +
        (actualBandEndpointTailBoundaryTrace globalBasis lambda sourceBasis
          globalN sourceN owner family).re := by
  have hgram := sourceBandGramResponse_eq_endpointCycle owner lambda family
  have hbase :
      (actualBandBaseRootLeg owner lambda).adjoint ∘L
          actualBandBaseRootLeg owner lambda -
        (actualBandBaseRootLeg owner lambda).adjoint ∘L
          (1 - basisPrefixProjection globalBasis globalN) ∘L
            actualBandBaseRootLeg owner lambda =
      (actualBandBaseRootLeg owner lambda).adjoint ∘L
        basisPrefixProjection globalBasis globalN ∘L
          actualBandBaseRootLeg owner lambda := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub]
    abel
  have hdual :
      (actualBandTargetFrameRootLeg owner lambda family).adjoint ∘L
          actualBandTargetDualRootLeg owner lambda family -
        (actualBandTargetFrameRootLeg owner lambda family).adjoint ∘L
          (1 - basisPrefixProjection globalBasis globalN) ∘L
            actualBandTargetDualRootLeg owner lambda family =
      (actualBandTargetFrameRootLeg owner lambda family).adjoint ∘L
        basisPrefixProjection globalBasis globalN ∘L
          actualBandTargetDualRootLeg owner lambda family := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub]
    abel
  have hbaseRe := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda =>
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN operator)).re)
    hbase
  have hdualRe := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda =>
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN operator)).re)
    hdual
  simp only [CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_sub, Complex.sub_re] at hbaseRe hdualRe
  rw [hgram]
  unfold actualBandEndpointBalancedPrefixTrace
    actualBandEndpointTailBoundaryTrace
  simp only [actualBandEndpointCycledResponse,
    rectangularPrefixTailBoundaryTrace,
    CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_sub, Complex.sub_re]
  linear_combination -hbaseRe + hdualRe

theorem sourceGram_add_tailBoundary_eq_balancedPrefixTrace
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
      actualBandEndpointBalancedPrefixTrace globalBasis lambda sourceBasis
        globalN sourceN owner family := by
  exact (actualBandEndpointBalancedPrefixTrace_eq_sourceGram_add_tailBoundary
    globalBasis lambda sourceBasis globalN sourceN owner family).symm

/- The balanced form remains connected to the complete signed crossing owner. -/
theorem balancedPrefixTrace_eq_two_integral_weightedBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointBalancedPrefixTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha family.visiblePrimes := by
  rw [actualBandEndpointBalancedPrefixTrace_eq_sourceGram_add_tailBoundary]
  exact sourceGram_add_tailBoundary_eq_two_integral_weightedBoundary
    globalBasis lambda sourceBasis globalN sourceN owner family

end CCM24FiniteSEndpointBalancedProjection
end CCM25Concrete
end Source
end ConnesWeilRH
