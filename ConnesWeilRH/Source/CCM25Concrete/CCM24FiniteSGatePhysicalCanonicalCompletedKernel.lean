/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCompletedKernelBridge

/-!
# Canonical completed-kernel diagonal readout for the finite-S target

The physical full-kernel formula requires a support window and several
Hilbert--Schmidt factorization witnesses.  The target diagonal itself is
canonical.  This file names that scalar and its source-basis diagonal series,
then proves every valid physical formula reads back to those canonical objects.

No basis independence of the ordinary diagonal series and no uniform estimate
are asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalCanonicalCompletedKernel

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalCompletedKernelBridge
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24SourceProlateTrace

/-- The completed physical scalar without a chosen support window or
factorization witness. -/
noncomputable def finiteEulerCanonicalCompletedKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) : ℂ :=
  inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family x)

/-- Every direct completed-kernel witness reads the canonical target diagonal.
The response remains source-prefix-free. -/
theorem finiteEulerCanonicalCompletedKernelScalar_eq_directLeakageDiagonal
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
    finiteEulerCanonicalCompletedKernelScalar owner lambda family x =
      inner ℂ x
        (finiteEulerCompletedKernelLeakageResponse owner lambda family a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor x) := by
  unfold finiteEulerCanonicalCompletedKernelScalar
  rw [finiteEulerTargetCommutatorResponse_eq_completedKernelLeakageResponse
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]

/-- Every physical full-kernel scalar is the canonical target diagonal.  Thus
the completed outer/reflected/prolate combination has no residual dependence
on the witness used to display it. -/
theorem finiteEulerCanonicalCompletedKernelScalar_eq_obliqueShearFullKernelScalar
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
    finiteEulerCanonicalCompletedKernelScalar owner lambda family x =
      sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c x := by
  calc
    finiteEulerCanonicalCompletedKernelScalar owner lambda family x =
        inner ℂ x
          (finiteEulerCompletedKernelLeakageResponse owner lambda family a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor x) :=
      finiteEulerCanonicalCompletedKernelScalar_eq_directLeakageDiagonal
        owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor x
    _ = sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c x :=
      inner_completedKernelLeakageResponse_eq_obliqueShearFullKernelScalar
        owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor x

/-- The source-basis diagonal series of the canonical completed scalar.  It is
canonical in the physical support/factorization witnesses, but still records
the named source basis required by `ordinaryTraceAlong`. -/
noncomputable def finiteEulerCanonicalCompletedKernelDiagonalSeries
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) : ℂ :=
  ∑' i, finiteEulerCanonicalCompletedKernelScalar owner lambda family
    (sourceBasis i)

/-- The actual target trace is definitionally the canonical completed diagonal
series along the same source basis. -/
theorem ordinaryTraceAlong_targetCommutator_eq_canonicalCompletedKernelDiagonalSeries
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      finiteEulerCanonicalCompletedKernelDiagonalSeries owner lambda family
        sourceBasis := by
  rw [ordinaryTraceAlong, finiteEulerCanonicalCompletedKernelDiagonalSeries]
  apply tsum_congr
  intro i
  rfl

/-- The existing physical full-kernel trace series is the canonical completed
diagonal series. -/
theorem finiteEulerCanonicalCompletedKernelDiagonalSeries_eq_obliqueShearFullKernelTrace
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    finiteEulerCanonicalCompletedKernelDiagonalSeries owner lambda family
        sourceBasis =
      finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis := by
  rw [finiteEulerCanonicalCompletedKernelDiagonalSeries,
    finiteEulerObliqueShearFullKernelTrace]
  apply tsum_congr
  intro i
  exact finiteEulerCanonicalCompletedKernelScalar_eq_obliqueShearFullKernelScalar
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor (sourceBasis i)

/-- Every direct completed-kernel response has the same source-basis diagonal
series, independently of the support/factorization witness used to construct
its physical formula. -/
theorem ordinaryTraceAlong_completedKernelLeakageResponse_eq_canonicalCompletedKernelDiagonalSeries
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerCompletedKernelLeakageResponse owner lambda family a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor) =
      finiteEulerCanonicalCompletedKernelDiagonalSeries owner lambda family
        sourceBasis := by
  rw [← finiteEulerTargetCommutatorResponse_eq_completedKernelLeakageResponse
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  exact ordinaryTraceAlong_targetCommutator_eq_canonicalCompletedKernelDiagonalSeries
    owner lambda family sourceBasis

end CCM24FiniteSGatePhysicalCanonicalCompletedKernel
end CCM25Concrete
end Source
end ConnesWeilRH
