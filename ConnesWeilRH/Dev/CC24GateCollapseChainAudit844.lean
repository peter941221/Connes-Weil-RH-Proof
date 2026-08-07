import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalTransportedOuterCollapse
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedKernelMovingBandGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace

open ConnesWeilRH Source CCM25Concrete
open CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
open CCM24FiniteSCanonicalTransportedOuterCollapse
open CCM24FiniteSCanonicalCompletedKernelMovingBandGuard

/-!
# 844 audit: the 3U Gate collapses to a single |sourceBand trace| bound,
and every structural step is axiom-clean; only ONE generic-lambda premise remains.

Chain (each `=` / `iff` / trace-equality is a named repo theorem):
  canonicalRealGate3UAt
    <-> |Tr(completedBoundaryCycle)| <= bound          (canonical ____________, see BoundaryCycle.lean:392)
    ==  (Tr(outer diff)).re - (Tr(moving band)).re     (ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving,
                                                         MovingBandGuard.lean:153)
  genuine finite-Euler transport  ==>  outerProjectionDifference = 0
    (actualOuterProjectionDifference_eq_zero, TransportedOuterCollapse.lean:170)
  hence Gate <-> |Tr(movingBand)| <= 1, and movingBand telescopes to
  rootSandwichedBandResponse / sourceBandGramResponse (sourceBand::recycle).

  The trace-class carrier is the finite-Euler completed-boundary pair
  (finiteEulerCompletedKernelBoundaryCyclePairData), which is built from a
  HILBERT-SCHMIDT factor pair; its summability is exactly
      hfactor : Summable fun i => ||sourceProlateHilbertSchmidtFactor lambda (globalBasis i)|| ^ 2
  This is the single-and-only open premise of the whole 3U chain
  (sourceProlateTrace.lean:74, sourceTwoBranchCommutator_isTraceClassAlong:332).

This file does not close hfactor; it records that the closure is ONE premise.
-/

-- Gate <-> completed-boundary real trace bound (the central door)
#check @canonicalRealGate3UAt_iff_completedBoundaryCycleRealBound

-- completed boundary trace = outer - moving (with genuine transport outer = 0)
#check @ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving
#check @actualOuterProjectionDifference_eq_zero
#check @actualMovingOuterBandDifference_eq_fixed
#check @actualRootSandwichedOuterProjectionDifference_eq_zero

-- collapse to sourceBand already recorded in the repo Audit
#check @ordinaryTraceAlong_completedBoundaryCycle_re_eq_neg_actualMoving

-- the only trace-class input left
#check @CCM24SourceProlateTrace.sourceThreeBranchCommutator_isTraceClassAlong
#check @CCM24SourceProlateTrace.sourceThreeBranchCommutator_isTraceClassAlong_of_prolateRemainder
#check @CCM24SourceProlateTrace.sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong

-- axiom hygiene of the collapse chain (must be [propext, Classical.choice, Quot.sound])
#print axioms canonicalRealGate3UAt_iff_completedBoundaryCycleRealBound
#print axioms ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving
#print axioms actualOuterProjectionDifference_eq_zero
#print axioms ordinaryTraceAlong_completedBoundaryCycle_re_eq_neg_actualMoving

theorem audit844_structure : True := by trivial