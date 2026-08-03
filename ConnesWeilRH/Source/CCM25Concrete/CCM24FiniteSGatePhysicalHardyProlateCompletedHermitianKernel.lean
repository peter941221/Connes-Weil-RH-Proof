/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalTargetHermitianPrefix

/-!
# Hermitian completed-kernel form of the Hardy--prolate row

The real Gate scalar uses the Hermitian part of the literal target.  This
module keeps that part on the same completed Hardy--prolate row and the same
three-branch physical boundary kernel as Proof 782.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianKernel

open scoped InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalCompletedKernelBridge
open CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
open CCM24FiniteSGatePhysicalHardyProlateCompletedComplement
open CCM24FiniteSGatePhysicalHardyProlateRow
open CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout
open CCM24FiniteSGatePhysicalTargetHermitianPrefix
open CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem adjoint_neg_eq_neg_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    (-operator)† = -(operator†) := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]

/-- The completed physical boundary operator retains the skew orientation of
the source commutator. -/
theorem sourceCompletedSignedKernelBoundaryOperator_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor)† =
      -sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor := by
  let kernel := sourceCompletedSignedKernelBoundaryOperator owner lambda a c
    hac hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  let boundary := sourceBoundaryCommutator owner lambda
  have hboundary : boundary = -kernel := by
    dsimp only [boundary, kernel]
    exact sourceBoundaryCommutator_eq_neg_completedKernelBoundaryOperator owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hkernel : kernel = -boundary := by
    have hneg := congrArg Neg.neg hboundary
    simpa only [neg_neg] using hneg.symm
  change kernel† = -kernel
  calc
    kernel† = (-boundary)† := by rw [hkernel]
    _ = -(boundary†) := adjoint_neg_eq_neg_adjoint boundary
    _ = -(-boundary) := by rw [sourceBoundaryCommutator_adjoint_eq_neg]
    _ = -kernel := by rw [← hkernel]

/-- The Hermitian target remains one bidirectional completed Hardy/prolate
row against the same three-branch physical kernel. -/
noncomputable def finiteEulerCausalHardyProlateCompletePhysicalHermitianResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iotaR kappaR tauR nu : Type*}
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  let A := finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family
  let Q := finiteEulerCausalHardyProlateTransportLift lambda family ∘L
    sourceHardyProlateComplementAnalysis lambda
  let K := sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  let J := sourceInclusion lambda
  (1 / 2 : ℂ) •
    (-((A†) ∘L Q ∘L K ∘L J) + J† ∘L K ∘L Q† ∘L A)

/-- The literal real Gate owner is the Hermitian completed-row response. -/
theorem finiteEulerTargetHermitianResponse_eq_completePhysicalHermitianResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    finiteEulerTargetHermitianResponse owner lambda family =
      finiteEulerCausalHardyProlateCompletePhysicalHermitianResponse owner lambda
        family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor := by
  let A := finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family
  let Q := finiteEulerCausalHardyProlateTransportLift lambda family ∘L
    sourceHardyProlateComplementAnalysis lambda
  let K := sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  let J := sourceInclusion lambda
  have htarget : finiteEulerTargetCommutatorResponse owner lambda family =
      -(A† ∘L Q ∘L K ∘L J) := by
    dsimp only [A, Q, K, J]
    exact target_eq_completePhysicalBoundaryRowCorner owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hkernel : K† = -K := by
    dsimp only [K]
    exact sourceCompletedSignedKernelBoundaryOperator_adjoint_eq_neg owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hadjoint : (-(A† ∘L Q ∘L K ∘L J))† =
      J† ∘L K ∘L Q† ∘L A := by
    rw [adjoint_neg_eq_neg_adjoint]
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hkernel]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      map_neg, neg_neg]
  rw [finiteEulerTargetHermitianResponse, htarget, hadjoint]
  rfl

/-- Every real Gate diagonal is the real part of one completed physical
Hardy/prolate pairing. -/
theorem inner_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetHermitianResponse owner lambda family x) =
      ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing owner lambda
        family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor x x).re : ℂ) := by
  rw [inner_targetHermitianResponse_eq_target_re,
    inner_target_eq_completePhysicalBoundaryPairing owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]

end CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianKernel
end CCM25Concrete
end Source
end ConnesWeilRH
