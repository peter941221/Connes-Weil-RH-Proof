/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandRootCycleDefect
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle

/-!
# Rectangular finite-prefix trace cycles

The ambient quadratic response and its source-Sonin readback are related by
rectangular factor cycles.  This module performs those cycles only on finite
source and target prefixes and records the exact product defects on both
carriers.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRectangularPrefixCycle

open CC20Concrete
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Matrix of a rectangular operator between two ordered Hilbert-basis
prefixes. -/
noncomputable def rectangularPrefixMatrix
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (operator : H →L[ℂ] G) :
    Matrix (Fin targetN) (Fin sourceN) ℂ :=
  fun i j => ⟪targetBasis (i : ℕ), operator (sourceBasis (j : ℕ))⟫_ℂ

/-- Failure of rectangular prefix multiplication on the target carrier. -/
noncomputable def rectangularTargetProductDefect
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) : Matrix (Fin targetN) (Fin targetN) ℂ :=
  basisPrefixMatrix targetBasis targetN (forward ∘L reverse) -
    rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward *
      rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse

/-- Failure of rectangular prefix multiplication on the source carrier. -/
noncomputable def rectangularSourceProductDefect
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) : Matrix (Fin sourceN) (Fin sourceN) ℂ :=
  basisPrefixMatrix sourceBasis sourceN (reverse ∘L forward) -
    rectangularPrefixMatrix targetBasis sourceBasis targetN sourceN reverse *
      rectangularPrefixMatrix sourceBasis targetBasis sourceN targetN forward

/-- Scalar discrepancy left by cycling a rectangular product between two
independently truncated carriers. -/
noncomputable def rectangularPrefixCycleBoundaryTrace
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) : ℂ :=
  Matrix.trace (rectangularTargetProductDefect sourceBasis targetBasis
    sourceN targetN forward reverse) -
  Matrix.trace (rectangularSourceProductDefect sourceBasis targetBasis
    sourceN targetN forward reverse)

/-- A rectangular finite-prefix trace cycle keeps both carrier-boundary
defects. -/
theorem trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (sourceBasis : HilbertBasis ℕ ℂ H)
    (targetBasis : HilbertBasis ℕ ℂ G)
    (sourceN targetN : ℕ) (forward : H →L[ℂ] G)
    (reverse : G →L[ℂ] H) :
    Matrix.trace
        (basisPrefixMatrix targetBasis targetN (forward ∘L reverse)) =
      Matrix.trace
          (basisPrefixMatrix sourceBasis sourceN (reverse ∘L forward)) +
        rectangularPrefixCycleBoundaryTrace sourceBasis targetBasis
          sourceN targetN forward reverse := by
  unfold rectangularPrefixCycleBoundaryTrace rectangularTargetProductDefect
    rectangularSourceProductDefect
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm]
  ring

theorem basisPrefixMatrix_add
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (left right : H →L[ℂ] H) :
    basisPrefixMatrix basis N (left + right) =
      basisPrefixMatrix basis N left + basisPrefixMatrix basis N right := by
  ext i j
  simp [basisPrefixMatrix, inner_add_right]

/-- The four rectangular factor cycles of the actual quadratic response,
with their original signs. -/
noncomputable def actualBandQuadraticRectangularBoundaryTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : ℂ :=
  rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandJetRootLeg owner lambda family)
      (actualBandBaseRootLeg owner lambda).adjoint +
    rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandJetRootLeg owner lambda family).adjoint -
    rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandBaseRootLeg owner lambda).adjoint +
    rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandTargetDualRootLeg owner lambda family)
      (actualBandTargetFrameRootLeg owner lambda family).adjoint

/-- The ambient quadratic prefix trace equals the source quadratic prefix
trace plus the complete four-cycle boundary discrepancy. -/
theorem trace_actualBandQuadraticRootResponse_eq_sourceCycle_add_boundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix globalBasis globalN
        (actualBandQuadraticRootResponse owner lambda family)) =
      Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (actualBandQuadraticCycledResponse owner lambda family)) +
        actualBandQuadraticRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family := by
  have hjetBase :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandJetRootLeg owner lambda family)
      (actualBandBaseRootLeg owner lambda).adjoint
  have hbaseJet :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandJetRootLeg owner lambda family).adjoint
  have hbaseBase :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandBaseRootLeg owner lambda).adjoint
  have hdualFrame :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandTargetDualRootLeg owner lambda family)
      (actualBandTargetFrameRootLeg owner lambda family).adjoint
  rw [actualBandQuadraticRootResponse_eq_rectangularFactors]
  unfold actualBandQuadraticCycledResponse actualBandFirstJetCycledResponse
    actualBandEndpointCycledResponse
    actualBandQuadraticRectangularBoundaryTrace
  simp only [basisPrefixMatrix_add,
    CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_add, Matrix.trace_sub]
  linear_combination hjetBase + hbaseJet - hbaseBase + hdualFrame

/-- The actual endpoint prefix is the ambient first jet minus the source
quadratic cycle and its complete rectangular boundary discrepancy. -/
theorem trace_rootSandwichedBandResponse_eq_firstJet_sub_sourceCycle_sub_boundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix globalBasis globalN
        (rootSandwichedBandResponse owner lambda family)) =
      Matrix.trace (basisPrefixMatrix globalBasis globalN
          (actualBandFirstJetRootResponse owner lambda family)) -
        Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (actualBandQuadraticCycledResponse owner lambda family)) -
        actualBandQuadraticRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family := by
  have hquadratic :=
    trace_actualBandQuadraticRootResponse_eq_sourceCycle_add_boundary
      globalBasis lambda sourceBasis globalN sourceN owner family
  rw [actualBandQuadraticRootResponse_eq_first_sub_endpoint,
    CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_sub] at hquadratic
  linear_combination -hquadratic

end CCM24FiniteSRectangularPrefixCycle
end CCM25Concrete
end Source
end ConnesWeilRH
