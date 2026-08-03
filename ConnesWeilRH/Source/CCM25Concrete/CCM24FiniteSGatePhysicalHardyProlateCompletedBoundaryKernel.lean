/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateCompletedComplement
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCompletedKernelBridge

/-!
# Physical completed-kernel form of the Hardy--prolate complement row

Proof 781 turns the root-local row into one source boundary commutator.
This module inserts the existing exact three-branch physical kernel for that
same commutator, retaining the whole signed row.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel

open scoped InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalCompletedKernelBridge
open CCM24FiniteSGatePhysicalHardyProlateCompletedComplement
open CCM24FiniteSGatePhysicalHardyProlateRow
open CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete physical boundary pairing.  The negative sign is the exact
orientation change from the target commutator `[W,R]` to the completed kernel
orientation `[R,W]`. -/
noncomputable def finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x y : sourceSoninCarrier lambda) : ℂ :=
  -inner ℂ
    (finiteEulerCausalHardyProlateRowLeft lambda family
      (finiteEulerDualFrame lambda family x))
    (finiteEulerCausalHardyProlateTransportLift lambda family
      (sourceHardyProlateComplementAnalysis lambda
        (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor (sourceInclusion lambda y))))

/-- The literal target is one completed Hardy/prolate row against the actual
three-branch physical boundary kernel. -/
theorem target_eq_completePhysicalBoundaryRowCorner
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
    finiteEulerTargetCommutatorResponse owner lambda family =
      -(((finiteEulerCausalHardyProlateRowLeft lambda family ∘L
        finiteEulerDualFrame lambda family).adjoint) ∘L
          finiteEulerCausalHardyProlateTransportLift lambda family ∘L
            sourceHardyProlateComplementAnalysis lambda ∘L
              sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
                reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
                globalBasis hfactor ∘L sourceInclusion lambda) := by
  rw [target_eq_completeBoundaryRowCorner,
    sourceBoundaryCommutator_eq_neg_completedKernelBoundaryOperator
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]

/-- Every literal target coefficient is the one signed physical completed
boundary pairing. -/
theorem inner_target_eq_completePhysicalBoundaryPairing
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
    (x y : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family y) =
      finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing owner lambda
        family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor x y := by
  unfold finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
  rw [target_eq_completePhysicalBoundaryRowCorner owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  let A := finiteEulerCausalHardyProlateRowLeft lambda family ∘L
    finiteEulerDualFrame lambda family
  let q := finiteEulerCausalHardyProlateTransportLift lambda family
    (sourceHardyProlateComplementAnalysis lambda
      (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor (sourceInclusion lambda y)))
  change inner ℂ x (-(A.adjoint q)) = -inner ℂ (A x) q
  rw [inner_neg_right]
  exact congrArg Neg.neg (A.adjoint_inner_right x q)

/-- The ordinary target trace is the diagonal series of the one signed
physical completed-boundary pairing. -/
theorem ordinaryTraceAlong_target_eq_completePhysicalBoundaryPairing
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ∑' i, finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing owner lambda
        family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor (sourceBasis i) (sourceBasis i) := by
  unfold ordinaryTraceAlong
  apply tsum_congr
  intro i
  exact inner_target_eq_completePhysicalBoundaryPairing owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
    (sourceBasis i) (sourceBasis i)

end CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
end CCM25Concrete
end Source
end ConnesWeilRH
