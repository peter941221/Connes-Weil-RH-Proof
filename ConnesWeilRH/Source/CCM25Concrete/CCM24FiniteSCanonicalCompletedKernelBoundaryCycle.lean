/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalAdjointEnergyGate

/-!
# Canonical completed-kernel boundary cycle

The completed physical target pair is genuinely Hilbert--Schmidt on both
legs. Its trace can therefore be cycled from the source Sonin carrier to the
common completed-boundary carrier. This produces a source-basis-independent
owner for the same signed scalar while retaining every physical branch.

This is not the ambient endpoint cycle: the new operator lives on the common
completed-boundary carrier and is defined from the exact target pair. No
escaping rectangular term is discarded. The module proves an equivalent
canonical real Gate contract, not its uniform analytic estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalCompletedKernelBoundaryCycle

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality
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

/-! ## The source-basis-free boundary operator -/

/-- The exact cyclic operator on the common completed-boundary carrier.
Unlike the ambient endpoint response, this is defined directly from the two
Hilbert--Schmidt legs of the canonical target pair. -/
noncomputable def finiteEulerCompletedKernelTargetBoundaryCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : R) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    commonBoundaryCarrier a c →L[C] commonBoundaryCarrier a c := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let right := base.right ∘L sourceInclusion lambda
  let leftAdjoint :=
    (sourcePhysicalCoframeLeakage lambda family).adjoint ∘L base.left.adjoint
  exact -(right ∘L leftAdjoint)

/-- Cycling the canonical source pair lands on the literal completed-boundary
operator.  This is the rectangular `BA†` side of the source `A†B` target. -/
theorem finiteEulerCompletedKernelTargetPairData_cyclic_eq
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    let pair := finiteEulerCompletedKernelTargetPairData owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
    pair.right ∘L pair.left.adjoint =
      finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerCompletedKernelTargetPairData,
    finiteEulerCompletedKernelTargetBoundaryCycle,
    BasisHilbertSchmidtPairData.smulRight,
    BasisHilbertSchmidtPairData.boundedPrecomp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply,
    neg_one_smul,
    ContinuousLinearMap.neg_apply]

/-- A pair on the completed-boundary carrier whose trace product is the
cyclic boundary operator. -/
noncomputable def finiteEulerCompletedKernelBoundaryCyclePairData
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    BasisHilbertSchmidtPairData
      (G := sourceSoninCarrier lambda) boundaryBasis :=
  let sourcePair := finiteEulerCompletedKernelTargetPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  { left := sourcePair.right.adjoint
    right := sourcePair.left.adjoint
    left_summable_normSq :=
      BasisHilbertSchmidtPairData.summable_adjoint_normSq sourceBasis
        boundaryBasis sourcePair.right sourcePair.right_summable_normSq
    right_summable_normSq :=
      BasisHilbertSchmidtPairData.summable_adjoint_normSq sourceBasis
        boundaryBasis sourcePair.left sourcePair.left_summable_normSq }

/-- The boundary pair owns the literal source-basis-free cyclic operator. -/
theorem finiteEulerCompletedKernelBoundaryCyclePairData_traceProduct_eq
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    (finiteEulerCompletedKernelBoundaryCyclePairData owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor).traceProduct =
      finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor := by
  rw [finiteEulerCompletedKernelBoundaryCyclePairData,
    BasisHilbertSchmidtPairData.traceProduct,
    ContinuousLinearMap.adjoint_adjoint]
  exact finiteEulerCompletedKernelTargetPairData_cyclic_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor

/-! ## Exact trace cycles and basis independence -/

/-- The source target trace cycles exactly to the completed-boundary carrier.
This uses the pair's absolutely summable two-basis coefficient matrix. -/
theorem ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor) := by
  let pair := finiteEulerCompletedKernelTargetPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  calc
    _ = ordinaryTraceAlong sourceBasis pair.traceProduct := by
      rw [show pair.traceProduct =
          finiteEulerTargetCommutatorResponse owner lambda family by
        dsimp only [pair]
        exact finiteEulerCompletedKernelTargetPairData_traceProduct_eq owner
          lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor]
    _ = ordinaryTraceAlong boundaryBasis
        (pair.right ∘L pair.left.adjoint) :=
      pair.ordinaryTraceAlong_traceProduct_eq_cyclic boundaryBasis
    _ = _ := by
      exact congrArg (ordinaryTraceAlong boundaryBasis)
        (finiteEulerCompletedKernelTargetPairData_cyclic_eq owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor)

/-- The cyclic boundary operator has a summable diagonal on every supplied
boundary basis. -/
theorem finiteEulerCompletedKernelTargetBoundaryCycle_isTraceClassAlong
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    IsTraceClassAlong boundaryBasis
      (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor) := by
  rw [← finiteEulerCompletedKernelBoundaryCyclePairData_traceProduct_eq owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact (finiteEulerCompletedKernelBoundaryCyclePairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor).traceProduct_isTraceClassAlong

/-- The canonical target trace is independent of the chosen source Hilbert
basis once both traces use the same completed physical owner. -/
theorem ordinaryTraceAlong_targetCommutator_sourceBasis_independent
    {rho sigma : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
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
    (firstBasis : HilbertBasis rho C (sourceSoninCarrier lambda))
    (secondBasis : HilbertBasis sigma C (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    ordinaryTraceAlong firstBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ordinaryTraceAlong secondBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) := by
  rw [ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis firstBasis hfactor,
    ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis secondBasis hfactor]

/-- The boundary trace itself is independent of the supplied boundary basis. -/
theorem ordinaryTraceAlong_completedBoundaryCycle_basis_independent
    {rho mu omega : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : R) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (firstBoundaryBasis : HilbertBasis mu C (commonBoundaryCarrier a c))
    (secondBoundaryBasis : HilbertBasis omega C (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho C (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    ordinaryTraceAlong firstBoundaryBasis
        (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor) =
      ordinaryTraceAlong secondBoundaryBasis
        (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor) := by
  rw [← ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis firstBoundaryBasis sourceBasis hfactor,
    ← ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis secondBoundaryBasis sourceBasis hfactor]

/-- The canonical real Gate is exactly the real trace bound for the completed
boundary-cycle owner. This equivalence retains the full signed pair. -/
theorem canonicalRealGate3UAt_iff_completedBoundaryCycleRealBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
    (bound : R) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |(ordinaryTraceAlong boundaryBasis
        (finiteEulerCompletedKernelTargetBoundaryCycle owner lambda
          (canonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis hfactor)).re| <= bound := by
  unfold canonicalRealGate3UAt
  rw [ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle owner
    lambda (canonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor]

end CCM24FiniteSCanonicalCompletedKernelBoundaryCycle
end CCM25Concrete
end Source
end ConnesWeilRH
