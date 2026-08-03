/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedKernelMovingBandGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedRadialSupport

/-!
# Collapse of the canonical transported outer projection

The synchronized finite Euler equivalence and its inverse preserve the actual
upper radial-support subspace.  Its Gram-corrected transported orthogonal
projection is therefore the original radial-support projection at every legal
time slice.  In particular, Proof 766's outer endpoint anomaly vanishes for
the genuine finite Euler transport at the projection level.

This identifies the transported outer projection and the resulting formal
band difference only.  It does not identify this projection-level candidate
with Proof 262's dual-coframe/nested-band carrier, whose adjoint and causal
orientation are guarded by Proof 743.

This source-specific collapse does not hold in periodic finite-section models,
where a one-sided invariant half-line is unavailable.  No trace estimate or
Gate 3U bound is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalTransportedOuterCollapse

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
open CCM24FiniteSCanonicalCompletedKernelMovingBandGuard
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandCalculus
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedRadialSupport
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

local notation "C" => ℂ
local notation "R" => ℝ

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Source-specific outer projection -/

/-- The Gram-corrected orthogonal projection onto the synchronized finite
Euler image of the source radial-support space. -/
noncomputable def parameterizedTransportedOuterProjection
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    finiteSCarrier →L[C] finiteSCarrier :=
  _root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection
    (parameterizedFiniteEulerEquiv alpha S halpha)
    (ccm24LogRadialSupportClosedSubspace lambda)

/-- The transported outer projection is an actual orthogonal projection. -/
theorem parameterizedTransportedOuterProjection_isStarProjection
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    IsStarProjection
      (parameterizedTransportedOuterProjection lambda alpha S halpha) := by
  exact
    _root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection_isStarProjection
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24LogRadialSupportClosedSubspace lambda)

/-- Both the transport and its inverse preserve radial support, so the range
of the transported orthogonal projection is exactly the original range. -/
theorem parameterizedTransportedOuterProjection_range
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    (parameterizedTransportedOuterProjection lambda alpha S halpha).range =
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule := by
  rw [parameterizedTransportedOuterProjection,
    _root_.ConnesWeilRH.CC20Concrete.transportedSoninStarProjection_range]
  change
    (ClosedSubmodule.mapEquiv
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24LogRadialSupportClosedSubspace lambda)).toSubmodule =
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
  rw [parameterizedFiniteEulerEquiv_maps_radialSupport]

/-- The canonical transported outer projection is literally fixed at every
legal synchronized time. -/
theorem parameterizedTransportedOuterProjection_eq_fixed
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    parameterizedTransportedOuterProjection lambda alpha S halpha =
      radialSupportProjection lambda := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (parameterizedTransportedOuterProjection_isStarProjection
      lambda alpha S halpha)
    (radialSupportProjection_isStarProjection lambda)
  rw [parameterizedTransportedOuterProjection_range,
    radialSupportProjection, Submodule.range_starProjection]

/-- Endpoint form of the transported outer projection for the finite family
owned by the arithmetic ledger. -/
noncomputable def finiteEulerTransportedOuterProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[C] finiteSCarrier :=
  parameterizedTransportedOuterProjection lambda 1 family.visiblePrimes
    (by norm_num)

/-- The endpoint transported outer projection is the fixed radial projection. -/
theorem finiteEulerTransportedOuterProjection_eq_fixed
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTransportedOuterProjection lambda family =
      radialSupportProjection lambda := by
  exact parameterizedTransportedOuterProjection_eq_fixed
    lambda 1 family.visiblePrimes (by norm_num)

/-! ## Transported band collapse -/

/-- Difference of the transported outer and transported Sonin projections.
This is the projection-level candidate suggested by Proof 262's notation; no
dual-coframe or nested-band carrier identification is asserted here. -/
noncomputable def parameterizedTransportedBandProjection
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    finiteSCarrier →L[C] finiteSCarrier :=
  parameterizedTransportedOuterProjection lambda alpha S halpha -
    CCM24FiniteSGramProjectionCalculus.parameterizedCanonicalGramProjection
      lambda alpha S

/-- The source-specific transported band is the repository's existing
fixed-outer moving Sonin band at every legal time. -/
theorem parameterizedTransportedBandProjection_eq_soninBand
    (lambda : CCM24SoninScale) (alpha : R)
    (S : List CCM24VisiblePrime) (halpha : |alpha| <= 1) :
    parameterizedTransportedBandProjection lambda alpha S halpha =
      parameterizedSoninBand lambda alpha S := by
  rw [parameterizedTransportedBandProjection,
    parameterizedTransportedOuterProjection_eq_fixed]
  rfl

/-- The transported band starts at the source Sonin band. -/
theorem parameterizedTransportedBandProjection_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    parameterizedTransportedBandProjection lambda 0 S (by norm_num) =
      sourceBandProjection lambda := by
  rw [parameterizedTransportedBandProjection_eq_soninBand,
    parameterizedSoninBand_zero]

/-- The transported band ends at the actual finite-S Sonin band. -/
theorem parameterizedTransportedBandProjection_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedTransportedBandProjection lambda 1 family.visiblePrimes
        (by norm_num) =
      targetBandProjection lambda family := by
  rw [parameterizedTransportedBandProjection_eq_soninBand,
    parameterizedSoninBand_one]

/-- Proof 766's arbitrary outer anomaly vanishes on the genuine transported
outer projection. -/
theorem actualOuterProjectionDifference_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    outerProjectionDifference lambda
        (finiteEulerTransportedOuterProjection lambda family) = 0 := by
  rw [outerProjectionDifference,
    finiteEulerTransportedOuterProjection_eq_fixed, sub_self]

/-- Consequently the projection-level transported-band endpoint is the
current fixed-outer route endpoint, not a third projection response. -/
theorem actualMovingOuterBandDifference_eq_fixed
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    movingOuterBandDifference lambda family
        (finiteEulerTransportedOuterProjection lambda family) =
      soninBandDifference lambda family := by
  exact (movingOuterBandDifference_eq_fixed_iff lambda family _).2
    (finiteEulerTransportedOuterProjection_eq_fixed lambda family)

/-! ## Root-smoothed and trace readout -/

/-- Root smoothing preserves the zero outer anomaly. -/
theorem actualRootSandwichedOuterProjectionDifference_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rootSandwichedOuterProjectionDifference owner lambda
        (finiteEulerTransportedOuterProjection lambda family) = 0 := by
  rw [rootSandwichedOuterProjectionDifference,
    actualOuterProjectionDifference_eq_zero]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    map_zero]

/-- The projection-level transported-band root response is exactly the
existing root-sandwiched finite-S band response. -/
theorem actualRootSandwichedMovingOuterBandResponse_eq_fixed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    rootSandwichedMovingOuterBandResponse owner lambda family
        (finiteEulerTransportedOuterProjection lambda family) =
      rootSandwichedBandResponse owner lambda family := by
  rw [rootSandwichedMovingOuterBandResponse,
    actualMovingOuterBandDifference_eq_fixed,
    rootSandwichedBandResponse]

/-- The zero outer anomaly is trace-legal in every named global Hilbert basis. -/
theorem actualRootSandwichedOuterProjectionDifference_isTraceClassAlong
    {nu : Type*} (globalBasis : HilbertBasis nu C finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsTraceClassAlong globalBasis
      (rootSandwichedOuterProjectionDifference owner lambda
        (finiteEulerTransportedOuterProjection lambda family)) := by
  rw [actualRootSandwichedOuterProjectionDifference_eq_zero]
  exact isTraceClassAlong_zero globalBasis

/-- The named-basis trace of the genuine outer anomaly is zero. -/
theorem ordinaryTraceAlong_actualRootSandwichedOuterProjectionDifference_eq_zero
    {nu : Type*} (globalBasis : HilbertBasis nu C finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ordinaryTraceAlong globalBasis
        (rootSandwichedOuterProjectionDifference owner lambda
          (finiteEulerTransportedOuterProjection lambda family)) = 0 := by
  rw [actualRootSandwichedOuterProjectionDifference_eq_zero,
    ordinaryTraceAlong]
  simp

/-- Source-specific projection-level correction of Proof 766: under the
explicit source-to-ambient cycle, the completed boundary trace is the negative
projection-level transported-band response because the outer anomaly is zero.
This is not Proof 262's missing dual-coframe carrier identification and does
not supply the Gate 3U estimate. -/
theorem ordinaryTraceAlong_completedBoundaryCycle_re_eq_neg_actualMoving
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
      -(ordinaryTraceAlong globalBasis
        (rootSandwichedMovingOuterBandResponse owner lambda family
          (finiteEulerTransportedOuterProjection lambda family))).re := by
  have h :=
    ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
      (finiteEulerTransportedOuterProjection lambda family)
      (actualRootSandwichedOuterProjectionDifference_isTraceClassAlong
        globalBasis owner lambda family)
      hfixed hsourceAmbientCycle
  rw [ordinaryTraceAlong_actualRootSandwichedOuterProjectionDifference_eq_zero]
    at h
  simpa using h

end CCM24FiniteSCanonicalTransportedOuterCollapse
end CCM25Concrete
end Source
end ConnesWeilRH
