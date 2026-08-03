/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedKernelBoundaryCycle

/-!
# Fixed-outer versus moving-outer band guard

The current finite-S route keeps the radial support projection fixed and moves
only the Sonin projection.  A transported-band endpoint instead moves both the
outer and Sonin projections.  Their difference is the genuine outer endpoint
anomaly.  This module records that term before any trace or estimate is taken.

The final theorem combines this algebra with Proof 765's completed-boundary
cycle.  It keeps the source-to-ambient endpoint cycle and trace legality as
explicit premises; no moving-band dual-coframe theorem is assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalCompletedKernelMovingBandGuard

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

local notation "C" => ℂ
local notation "R" => ℝ

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The missing outer endpoint -/

/-- Difference between a supplied moving outer projection and the fixed radial
support projection used by the current route. -/
noncomputable def outerProjectionDifference
    (lambda : CCM24SoninScale)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    finiteSCarrier →L[C] finiteSCarrier :=
  movingOuter - radialSupportProjection lambda

/-- Band difference obtained when both the supplied outer projection and the
actual finite-S Sonin projection are moved. -/
noncomputable def movingOuterBandDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    finiteSCarrier →L[C] finiteSCarrier :=
  (movingOuter - targetSoninProjection lambda family) -
    (radialSupportProjection lambda - sourceSoninProjection lambda)

/-- A moving-outer band differs from the route's fixed-outer band by exactly
the outer projection endpoint. -/
theorem movingOuterBandDifference_eq_outer_add_fixed
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    movingOuterBandDifference lambda family movingOuter =
      outerProjectionDifference lambda movingOuter +
        soninBandDifference lambda family := by
  unfold movingOuterBandDifference outerProjectionDifference
    soninBandDifference targetBandProjection sourceBandProjection
  abel

/-- Direct identification with the fixed-outer route is valid exactly when
the supplied outer endpoint itself is fixed. -/
theorem movingOuterBandDifference_eq_fixed_iff
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    movingOuterBandDifference lambda family movingOuter =
        soninBandDifference lambda family ↔
      movingOuter = radialSupportProjection lambda := by
  rw [movingOuterBandDifference_eq_outer_add_fixed]
  simp [outerProjectionDifference, sub_eq_zero]

/-! ## Root-smoothed operator ledger -/

/-- Root-smoothed response for the moving-outer band difference. -/
noncomputable def rootSandwichedMovingOuterBandResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    finiteSCarrier →L[C] finiteSCarrier :=
  rootConvolution owner ∘L
    movingOuterBandDifference lambda family movingOuter ∘L
      (rootConvolution owner)†

/-- Root-smoothed outer endpoint anomaly. -/
noncomputable def rootSandwichedOuterProjectionDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    finiteSCarrier →L[C] finiteSCarrier :=
  rootConvolution owner ∘L outerProjectionDifference lambda movingOuter ∘L
    (rootConvolution owner)†

/-- The same outer anomaly survives after root smoothing. -/
theorem rootSandwichedMovingOuterBandResponse_eq_outer_add_fixed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier) :
    rootSandwichedMovingOuterBandResponse owner lambda family movingOuter =
      rootSandwichedOuterProjectionDifference owner lambda movingOuter +
        rootSandwichedBandResponse owner lambda family := by
  rw [rootSandwichedMovingOuterBandResponse,
    movingOuterBandDifference_eq_outer_add_fixed]
  apply ContinuousLinearMap.ext
  intro u
  simp only [rootSandwichedOuterProjectionDifference,
    rootSandwichedBandResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- Once the two summands are trace-legal, the moving-band trace is their
literal sum.  This theorem does not manufacture either legality witness. -/
theorem ordinaryTraceAlong_movingOuterBandResponse_eq_add
    {nu : Type*} (globalBasis : HilbertBasis nu C finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier)
    (houter : IsTraceClassAlong globalBasis
      (rootSandwichedOuterProjectionDifference owner lambda movingOuter))
    (hfixed : IsTraceClassAlong globalBasis
      (rootSandwichedBandResponse owner lambda family)) :
    ordinaryTraceAlong globalBasis
        (rootSandwichedMovingOuterBandResponse owner lambda family
          movingOuter) =
      ordinaryTraceAlong globalBasis
          (rootSandwichedOuterProjectionDifference owner lambda movingOuter) +
        ordinaryTraceAlong globalBasis
          (rootSandwichedBandResponse owner lambda family) := by
  rw [rootSandwichedMovingOuterBandResponse_eq_outer_add_fixed]
  exact ordinaryTraceAlong_add globalBasis _ _ houter hfixed

/-! ## Corrected bridge from the completed boundary cycle -/

/-- The completed-boundary real trace equals outer endpoint minus moving-band
endpoint.  The formula displays the outer anomaly which a direct identification
with a transported-band dual-coframe expression would omit. -/
theorem ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : R) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (negativeBasis : HilbertBasis iota C
      (Lp C 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa C
      (Lp C 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau C
      (Lp C 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR C
      (Lp C 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR C
      (Lp C 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR C
      (Lp C 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu C finiteSCarrier)
    (boundaryBasis : HilbertBasis mu C (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho C (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2)
    (movingOuter : finiteSCarrier →L[C] finiteSCarrier)
    (houter : IsTraceClassAlong globalBasis
      (rootSandwichedOuterProjectionDifference owner lambda movingOuter))
    (hfixed : IsTraceClassAlong globalBasis
      (rootSandwichedBandResponse owner lambda family))
    (hsourceAmbientCycle :
      ordinaryTraceAlong sourceBasis
          (CCM24FiniteSBandTrace.sourceBandGramResponse owner lambda family) =
        ordinaryTraceAlong globalBasis
          (rootSandwichedBandResponse owner lambda family)) :
    (ordinaryTraceAlong boundaryBasis
      (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor)).re =
      (ordinaryTraceAlong globalBasis
        (rootSandwichedOuterProjectionDifference owner lambda
          movingOuter)).re -
      (ordinaryTraceAlong globalBasis
        (rootSandwichedMovingOuterBandResponse owner lambda family
          movingOuter)).re := by
  have hboundary := ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have htarget :=
    CCM24FiniteSCanonicalRealGate.ordinaryTraceAlong_targetCommutator_re_eq_neg_sourceBand_re
      owner lambda family sourceBasis
  have hmoving := ordinaryTraceAlong_movingOuterBandResponse_eq_add globalBasis
    owner lambda family movingOuter houter hfixed
  have hmovingRe := congrArg Complex.re hmoving
  calc
    _ = (ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re := by
      rw [hboundary]
    _ = -(ordinaryTraceAlong sourceBasis
        (CCM24FiniteSBandTrace.sourceBandGramResponse owner lambda family)).re :=
      htarget
    _ = -(ordinaryTraceAlong globalBasis
        (rootSandwichedBandResponse owner lambda family)).re := by
      rw [hsourceAmbientCycle]
    _ = _ := by
      simp only [Complex.add_re] at hmovingRe
      linarith

end CCM24FiniteSCanonicalCompletedKernelMovingBandGuard
end CCM25Concrete
end Source
end ConnesWeilRH
