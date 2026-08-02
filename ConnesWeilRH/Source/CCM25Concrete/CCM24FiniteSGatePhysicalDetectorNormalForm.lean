/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalBoundaryCenteredCycle

/-!
# Detector off-diagonal normal form for the Gate response

Proof 731 removes the fixed source-projection block from the physical boundary
trace.  On the source Sonin carrier the same centering removes the commutator
itself.  If `R = J J^dagger`, `K = [R,W]`, and both family-dependent coframes
land in the `R` complement, then

```text
GateResponse_S = J^dagger W U_S + F_S^dagger W J.
```

Here `U_S` is the complete endpoint cancellation residual and `F_S` is the
forward actual-band coframe.  The two terms remain in one operator.  No
separate absolute value, uniform estimate, finite-S sign, or RH premise is
asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalDetectorNormalForm

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGateBoundaryMomentBridge
open CCM24FiniteSGatePhysicalBoundaryCenteredCycle
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationBoundaryMomentBridge
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The exact source-carrier Gate owner after the fixed source projection and
the commutator notation have both been removed. -/
noncomputable def sourceGatePhysicalDetectorOffDiagonalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceEndpointCancellationResidual lambda family +
    (sourceActualBandForwardCoframe lambda family)† ∘L
      detectorOperator owner ∘L sourceInclusion lambda

/-- The adjoint of Proof 727's complete boundary moment is the detector-only
off-diagonal response. -/
theorem sourceEndpointCancellationBoundaryMoment_adjoint_eq_detectorOffDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceEndpointCancellationBoundaryMoment owner lambda family)† =
      sourceGatePhysicalDetectorOffDiagonalResponse owner lambda family := by
  have hadjointAdd
      (left right : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda) :
      (left + right)† = left† + right† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  unfold sourceEndpointCancellationBoundaryMoment
  rw [hadjointAdd]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq,
    ContinuousLinearMap.comp_assoc,
    sourceGatePhysicalDetectorOffDiagonalResponse]

/-- The Gate-facing response itself has the detector-only off-diagonal normal
form.  This is operator equality, not merely trace equality. -/
theorem lowerFactorGaugedResponse_eq_detectorOffDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      sourceGatePhysicalDetectorOffDiagonalResponse owner lambda family := by
  rw [lowerFactorGaugedResponse_eq_sourceEndpointCancellationBoundaryMoment_adjoint]
  exact sourceEndpointCancellationBoundaryMoment_adjoint_eq_detectorOffDiagonal
    owner lambda family

/-- Fixed-family trace legality is unchanged by the detector off-diagonal
normal form. -/
theorem lowerFactorGaugedResponse_isTraceClassAlong_iff_detectorOffDiagonal
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    IsTraceClassAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) ↔
      IsTraceClassAlong basis
        (sourceGatePhysicalDetectorOffDiagonalResponse
          owner lambda family) := by
  rw [lowerFactorGaugedResponse_eq_detectorOffDiagonal]

/-- The ordinary Gate trace is the ordinary trace of the detector-only
off-diagonal response. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_detectorOffDiagonal
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong basis
        (sourceGatePhysicalDetectorOffDiagonalResponse
          owner lambda family) := by
  rw [lowerFactorGaugedResponse_eq_detectorOffDiagonal]

/-- Every scalar trace-norm bound is equivalent for the Gate response and its
detector-only off-diagonal normal form. -/
theorem lowerFactorGaugedResponse_trace_norm_le_iff_detectorOffDiagonal
    {ι : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) (bound : ℝ) :
    ‖ordinaryTraceAlong basis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound ↔
      ‖ordinaryTraceAlong basis
        (sourceGatePhysicalDetectorOffDiagonalResponse
          owner lambda family)‖ ≤ bound := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_detectorOffDiagonal]

section BoundaryData

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {ι κ τ ιr κr τr ν μ ρ : Type*}
variable (negativeBasis : HilbertBasis ι ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis κ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis τ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis ιr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis κr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis τr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

/-- Proof 731's centered physical boundary trace and the detector-only source
trace are the same scalar. -/
theorem ordinaryTraceAlong_centeredBoundaryCycle_eq_detectorOffDiagonal :
    ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) =
      ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalDetectorOffDiagonalResponse
          owner lambda family) := by
  calc
    ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) =
        ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family) :=
      (ordinaryTraceAlong_lowerFactorGaugedResponse_eq_centeredBoundaryCycle
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor).symm
    _ = ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalDetectorOffDiagonalResponse
          owner lambda family) :=
      ordinaryTraceAlong_lowerFactorGaugedResponse_eq_detectorOffDiagonal
        owner lambda family sourceBasis

end BoundaryData

end CCM24FiniteSGatePhysicalDetectorNormalForm
end CCM25Concrete
end Source
end ConnesWeilRH
