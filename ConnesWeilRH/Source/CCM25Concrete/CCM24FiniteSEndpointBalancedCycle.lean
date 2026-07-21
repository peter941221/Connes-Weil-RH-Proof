/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointBalancedProjection

/-!
# Exact cycle of the balanced endpoint ledger

The balanced source-prefix term and its complementary target-prefix term are
one finite rectangular trace cycle.  This module performs that cycle through
the finite matrix products, so no infinite-dimensional trace cyclicity is
used.  The source cutoff therefore disappears from the balanced endpoint
ledger, which is exactly the target-prefix trace of the root-sandwiched
response.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointBalancedCycle

open CC20Concrete
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSRectangularPrefixCycle
open CCM24FiniteSRectangularTailFactorization
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSEndpointBalancedProjection

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source-prefix plus complementary target-prefix pairing for one
rectangular factor pair. -/
noncomputable def rectangularBalancedPrefixTrace
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ)
    (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) : ℂ :=
  Matrix.trace (basisPrefixMatrix sourceBasis sourceN
      (reverse ∘L basisPrefixProjection targetBasis targetN ∘L forward)) +
    Matrix.trace (basisPrefixMatrix targetBasis targetN
      (forward ∘L (1 - basisPrefixProjection sourceBasis sourceN) ∘L
        reverse))

/-- A finite rectangular cycle cancels its two intermediate-prefix products. -/
theorem rectangularBalancedPrefixTrace_eq_targetPrefixTrace
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ)
    (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    rectangularBalancedPrefixTrace sourceBasis targetBasis sourceN targetN
        forward reverse =
      Matrix.trace (basisPrefixMatrix targetBasis targetN
        (forward ∘L reverse)) := by
  have htail :
      forward ∘L (1 - basisPrefixProjection sourceBasis sourceN) ∘L reverse =
        (forward ∘L reverse) -
          (forward ∘L basisPrefixProjection sourceBasis sourceN ∘L reverse) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub]
  have hsource :=
    rectangularPrefixMatrix_mul_eq_sourceCompression_prefixProjection
      sourceBasis targetBasis sourceN targetN forward reverse
  have htarget :=
    rectangularPrefixMatrix_mul_eq_targetCompression_prefixProjection
      sourceBasis targetBasis sourceN targetN forward reverse
  unfold rectangularBalancedPrefixTrace
  rw [htail, CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    ← hsource, ← htarget, Matrix.trace_sub]
  have hcycle :
      Matrix.trace
          (rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse *
            rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward) =
        Matrix.trace
          (rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward *
            rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse) := by
    exact Matrix.trace_mul_comm _ _
  rw [hcycle]
  ring

/-- Proof 460's actual balanced ledger is the target-prefix trace of the
root-sandwiched endpoint response.  The source cutoff is only an internal
finite-cycle parameter. -/
theorem actualBandEndpointBalancedPrefixTrace_eq_targetPrefixRootResponse
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointBalancedPrefixTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      (Matrix.trace (basisPrefixMatrix globalBasis globalN
        (rootSandwichedBandResponse owner lambda family))).re := by
  rw [actualBandEndpointBalancedPrefixTrace]
  have hbase := rectangularBalancedPrefixTrace_eq_targetPrefixTrace
    sourceBasis globalBasis sourceN globalN
    (actualBandBaseRootLeg owner lambda)
    (actualBandBaseRootLeg owner lambda).adjoint
  have hdual := rectangularBalancedPrefixTrace_eq_targetPrefixTrace
    sourceBasis globalBasis sourceN globalN
    (actualBandTargetDualRootLeg owner lambda family)
    (actualBandTargetFrameRootLeg owner lambda family).adjoint
  unfold rectangularBalancedPrefixTrace at hbase hdual
  have hbaseRe := congrArg Complex.re hbase
  have hdualRe := congrArg Complex.re hdual
  simp only [Complex.add_re] at hbaseRe hdualRe
  rw [rootSandwichedBandResponse_eq_rectangularFactors]
  simp only [CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_sub, Complex.sub_re]
  linear_combination hbaseRe - hdualRe

/-- The target-prefix root response is the same complete weighted endpoint
owner as Proof 460's balanced ledger. -/
theorem targetPrefixRootResponse_eq_two_integral_weightedBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    (Matrix.trace (basisPrefixMatrix globalBasis globalN
      (rootSandwichedBandResponse owner lambda family))).re =
      2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha family.visiblePrimes := by
  rw [← actualBandEndpointBalancedPrefixTrace_eq_targetPrefixRootResponse
    globalBasis lambda sourceBasis globalN sourceN owner family]
  exact balancedPrefixTrace_eq_two_integral_weightedBoundary
    globalBasis lambda sourceBasis globalN sourceN owner family

end CCM24FiniteSEndpointBalancedCycle
end CCM25Concrete
end Source
end ConnesWeilRH
