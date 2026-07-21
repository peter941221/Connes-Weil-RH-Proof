/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedBoundaryLedger

/-!
# Endpoint-only rectangular boundary collapse

The four-factor quadratic ledger contains a first-jet pair and an endpoint
pair with opposite signs.  This module performs that cancellation exactly on
finite prefixes, leaving the source Gram endpoint and its two genuine carrier
defects.  The root-cycle defect remains on the integrated side of the same
identity.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointBoundaryCollapse

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSRectangularPrefixCycle
open CCM24FiniteSCombinedBoundaryLedger
open CCM24FiniteSMovingBandMatrixCancellation
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSCanonicalCompletedResponse

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/- The endpoint boundary is the exact difference of the two endpoint factor
   cycles; no first-jet factor is hidden in this definition. -/
noncomputable def actualBandEndpointRectangularBoundaryTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : ℂ :=
  rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandBaseRootLeg owner lambda).adjoint -
    rectangularPrefixCycleBoundaryTrace sourceBasis globalBasis sourceN globalN
      (actualBandTargetDualRootLeg owner lambda family)
      (actualBandTargetFrameRootLeg owner lambda family).adjoint

/-- The ambient endpoint trace cycles to the source endpoint cycle plus only
the two endpoint rectangular defects. -/
theorem trace_rootSandwichedBandResponse_eq_endpointCycle_add_boundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix globalBasis globalN
        (rootSandwichedBandResponse owner lambda family)) =
      Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (actualBandEndpointCycledResponse owner lambda family)) +
        actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family := by
  have hbase :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandBaseRootLeg owner lambda)
      (actualBandBaseRootLeg owner lambda).adjoint
  have hdual :=
    trace_basisPrefixMatrix_rectangularProduct_eq_cycled_add_boundary
      sourceBasis globalBasis sourceN globalN
      (actualBandTargetDualRootLeg owner lambda family)
      (actualBandTargetFrameRootLeg owner lambda family).adjoint
  rw [rootSandwichedBandResponse_eq_rectangularFactors]
  unfold actualBandEndpointCycledResponse
    actualBandEndpointRectangularBoundaryTrace
  simp only [CCM24FiniteSPrefixBoundaryDefect.basisPrefixMatrix_sub,
    Matrix.trace_sub]
  linear_combination hbase - hdual

/-- The Proof 457 carrier ledger is exactly the endpoint-only source cycle
plus its rectangular boundary, after the first-jet cancellation. -/
theorem actualBandEndpointCarrierLedgerTrace_eq_endpointCycle_add_boundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (actualBandEndpointCycledResponse owner lambda family))).re +
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re := by
  have hledger := congrArg Complex.re
    (trace_rootSandwichedBandResponse_eq_firstJet_sub_sourceCycle_sub_boundary
      globalBasis lambda sourceBasis globalN sourceN owner family)
  have hendpoint := congrArg Complex.re
    (trace_rootSandwichedBandResponse_eq_endpointCycle_add_boundary
      globalBasis lambda sourceBasis globalN sourceN owner family)
  simp only [Complex.sub_re, Complex.add_re] at hledger hendpoint
  unfold actualBandEndpointCarrierLedgerTrace
  linarith [hledger, hendpoint]

/-- The source endpoint cycle is the existing Gram response, so the collapsed
ledger has a direct source-owner form. -/
theorem actualBandEndpointCarrierLedgerTrace_eq_sourceGram_add_boundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (sourceBandGramResponse owner lambda family))).re +
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re := by
  have hcollapsed :=
    actualBandEndpointCarrierLedgerTrace_eq_endpointCycle_add_boundary
      globalBasis lambda sourceBasis globalN sourceN owner family
  have hgram := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda =>
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN operator)).re)
    (sourceBandGramResponse_eq_endpointCycle owner lambda family)
  calc
    actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (actualBandEndpointCycledResponse owner lambda family))).re +
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re := hcollapsed
    _ = (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
          (sourceBandGramResponse owner lambda family))).re +
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re := by
      have h := congrArg
        (fun value : ℝ => value +
          (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
            sourceBasis globalN sourceN owner family).re) hgram.symm
      simpa only using h

/-- The source-Gram form is still exactly the complete weighted crossing
integral, so the root-cycle defect remains coupled to the endpoint owner. -/
theorem sourceGram_add_boundary_eq_two_integral_weightedBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
        (sourceBandGramResponse owner lambda family))).re +
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re =
      2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha family.visiblePrimes := by
  calc
    (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
        (sourceBandGramResponse owner lambda family))).re +
          (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
            sourceBasis globalN sourceN owner family).re =
        actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
          globalN sourceN owner family := by
            rw [actualBandEndpointCarrierLedgerTrace_eq_sourceGram_add_boundary]
    _ = 2 * ∫ alpha : ℝ in 0..1,
          actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
            alpha family.visiblePrimes :=
      actualBandEndpointCarrierLedgerTrace_eq_two_integral_weightedBoundary
        globalBasis lambda sourceBasis globalN sourceN owner family

/-- Canonical consumer for a bound on the endpoint-only source Gram plus the
two rectangular boundary defects. -/
theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_sourceGramBoundaryBound
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
        (actualBandEndpointRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN (sourceCutoff globalN) owner
            (canonicalFamily owner)).re| ≤
        2 * ((owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3))) :
    ‖PositiveTrace.ordinaryTraceAlong globalBasis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  apply
    canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_weightedBoundaryBound
      globalBasis owner lambda htrace
  intro globalN
  have hledger :=
    sourceGram_add_boundary_eq_two_integral_weightedBoundary
      globalBasis lambda sourceBasis globalN (sourceCutoff globalN) owner
        (canonicalFamily owner)
  have hscaled :
      |2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha (canonicalFamily owner).visiblePrimes| ≤
        2 * ((owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) := by
    rw [← hledger]
    exact hbound globalN
  rw [abs_mul] at hscaled
  norm_num at hscaled
  nlinarith

end CCM24FiniteSEndpointBoundaryCollapse
end CCM25Concrete
end Source
end ConnesWeilRH
