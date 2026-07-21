/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRectangularPrefixCycle

/-!
# Combined finite-prefix carrier ledger

Proofs 455 and 456 expose two boundary ledgers on different sides of the
same endpoint: the root-cycle defect belongs to the complete crossing
integral, while the rectangular carrier defect belongs to the source Sonin
readback.  This module joins them before any absolute value is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCombinedBoundaryLedger

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSMovingBandMatrixCancellation
open CCM24FiniteSMovingBandRootCycleDefect
open CCM24FiniteSRectangularPrefixCycle

/- The endpoint ledger is deliberately a single scalar.  Its three displayed
   terms are not estimates; they are the exact signed carrier decomposition. -/
noncomputable def actualBandEndpointCarrierLedgerTrace
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : ℝ :=
  (Matrix.trace (basisPrefixMatrix globalBasis globalN
      (actualBandFirstJetRootResponse owner lambda family))).re -
    (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
      (actualBandQuadraticCycledResponse owner lambda family))).re -
    (actualBandQuadraticRectangularBoundaryTrace globalBasis lambda sourceBasis
      globalN sourceN owner family).re

/-- The rectangular carrier ledger and the root-cycle ledger are the same
signed finite-prefix scalar.  This is the exact combined owner used by the
next Gate 3U producer. -/
theorem actualBandEndpointCarrierLedgerTrace_eq_two_integral_weightedBoundary
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (globalN sourceN : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
        globalN sourceN owner family =
      2 * ∫ alpha : ℝ in 0..1,
        actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
          alpha family.visiblePrimes := by
  have hrect := congrArg Complex.re
    (trace_rootSandwichedBandResponse_eq_firstJet_sub_sourceCycle_sub_boundary
      globalBasis lambda sourceBasis globalN sourceN owner family)
  have hendpoint :=
    trace_basisPrefixMatrix_bandResponse_re_eq_two_integral_complete
      globalBasis owner lambda family globalN
  have hcycle :=
    integral_trace_actualCompletedRootCrossingOnUnit_re_eq_weightedBoundaryTrace
      globalBasis globalN owner lambda family.visiblePrimes
  simp only [Complex.sub_re] at hrect
  unfold actualBandEndpointCarrierLedgerTrace
  calc
    (Matrix.trace (basisPrefixMatrix globalBasis globalN
        (actualBandFirstJetRootResponse owner lambda family))).re -
          (Matrix.trace (basisPrefixMatrix sourceBasis sourceN
            (actualBandQuadraticCycledResponse owner lambda family))).re -
        (actualBandQuadraticRectangularBoundaryTrace globalBasis lambda
          sourceBasis globalN sourceN owner family).re =
        (Matrix.trace (basisPrefixMatrix globalBasis globalN
          (rootSandwichedBandResponse owner lambda family))).re := by
            linarith [hrect]
    _ = 2 * ∫ alpha : ℝ in 0..1,
          (Matrix.trace (basisPrefixMatrix globalBasis globalN
            (actualCompletedRootCrossingOnUnit owner lambda alpha
              family.visiblePrimes))).re := hendpoint
    _ = 2 * ∫ alpha : ℝ in 0..1,
          actualCompletedWeightedBoundaryTrace globalBasis globalN owner lambda
            alpha family.visiblePrimes := by
      rw [hcycle]

/-- A canonical consumer that accepts only the complete carrier ledger.  The
source response, rectangular defect, detector core, and root-cycle defect are
therefore bounded as one signed object. -/
theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_carrierLedgerBound
    (globalBasis : HilbertBasis ℕ ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (sourceCutoff : ℕ → ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (htrace : PositiveTrace.IsTraceClassAlong globalBasis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ globalN : ℕ,
      |actualBandEndpointCarrierLedgerTrace globalBasis lambda sourceBasis
          globalN (sourceCutoff globalN) owner (canonicalFamily owner)| ≤
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
    actualBandEndpointCarrierLedgerTrace_eq_two_integral_weightedBoundary
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

end CCM24FiniteSCombinedBoundaryLedger
end CCM25Concrete
end Source
end ConnesWeilRH
